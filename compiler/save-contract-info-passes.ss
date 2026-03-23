#!chezscheme

;;; This file is part of Compact.
;;; Copyright (C) 2025 Midnight Foundation
;;; SPDX-License-Identifier: Apache-2.0
;;; Licensed under the Apache License, Version 2.0 (the "License");
;;; you may not use this file except in compliance with the License.
;;; You may obtain a copy of the License at
;;;
;;; 	http://www.apache.org/licenses/LICENSE-2.0
;;;
;;; Unless required by applicable law or agreed to in writing, software
;;; distributed under the License is distributed on an "AS IS" BASIS,
;;; WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
;;; See the License for the specific language governing permissions and
;;; limitations under the License.

(library (save-contract-info-passes)
  (export save-contract-info-passes)
  (import (except (chezscheme) errorf)
          (utils)
          (datatype)
          (nanopass)
          (json)
          (langs)
          (compiler-version)
          (language-version)
          (runtime-version)
          (pass-helpers))

  ;; Strip the __compact_ prefix that analysis passes add to Cell
  (define (clean-adt-name sym)
    (let ([s (symbol->string sym)])
      (if (and (fx>= (string-length s) 10)
               (string=? (substring s 0 10) "__compact_"))
          (substring s 10 (string-length s))
          s)))

  ;; PascalCase ADT name -> kebab-case storage kind
  (define (adt-name->storage name)
    (cond
      [(string=? name "Cell") "cell"]
      [(string=? name "Counter") "counter"]
      [(string=? name "Map") "map"]
      [(string=? name "Set") "set"]
      [(string=? name "List") "list"]
      [(string=? name "MerkleTree") "merkle-tree"]
      [(string=? name "HistoricMerkleTree") "historic-merkle-tree"]
      [else (internal-errorf 'save-contract-info "unrecognized ledger ADT kind: ~a" name)]))

  ;; Return the type-specific JSON fields for a given ADT kind.
  ;; type-fn is the Type serializer (passed in so this can live outside define-pass).
  (define (adt-type-fields clean-name adt-arg* type-fn)
    (define (serialize-arg arg)
      (nanopass-case (Lnodisclose Public-Ledger-ADT-Arg) arg
        [,nat nat]
        [,type (type-fn type)]))
    (cond
      [(string=? clean-name "Cell")
       (list (cons "type" (serialize-arg (car adt-arg*))))]
      [(string=? clean-name "Counter")
       (list (cons "type" (list (cons "type-name" "Uint")
                                (cons "maxval" 18446744073709551615))))]
      [(string=? clean-name "Map")
       (list (cons "key-type" (serialize-arg (car adt-arg*)))
             (cons "value-type" (serialize-arg (cadr adt-arg*))))]
      [(or (string=? clean-name "Set") (string=? clean-name "List"))
       (list (cons "element-type" (serialize-arg (car adt-arg*))))]
      [(or (string=? clean-name "MerkleTree") (string=? clean-name "HistoricMerkleTree"))
       (list (cons "depth" (serialize-arg (car adt-arg*)))
             (cons "element-type" (serialize-arg (cadr adt-arg*))))]
      [else (internal-errorf 'save-contract-info "unrecognized ledger ADT kind: ~a" clean-name)]))

  ; NB: must come after identify-pure-circuits
  (define-pass save-contract-info : Lnodisclose (ir proof-circuit-name*) -> Lnodisclose ()
    (Program : Program (ir) -> Program ()
      [(program ,src (,contract-name* ...) ((,export-name* ,name*) ...) ,pelt* ...)
       (let ([op (get-target-port 'contract-info.json)])
         (print-json op
           (list
             (cons
               "compiler-version"
               compiler-version-string)
             (cons
               "language-version"
               language-version-string)
             (cons
               "runtime-version"
               runtime-version-string)
             (cons
               "circuits"
               (list->vector
                 (let ([export-alist (map cons export-name* name*)])
                   (fold-right
                     (lambda (pelt circuit*) (exported-circuit pelt circuit* export-alist))
                     '()
                     pelt*))))
             (cons
               "witnesses"
               (list->vector (fold-right Witness '() pelt*)))
             (cons
               "contracts"
               (list->vector (map symbol->string contract-name*)))
             (cons
               "ledger"
               (list->vector (fold-right LedgerField '() pelt*))))))
       ir])
    (Witness : Program-Element (ir witness*) -> * (json)
      [(witness ,src ,function-name (,arg* ...) ,type)
       (cons
         (list
           (cons
             "name"
             (symbol->string (id-sym function-name)))
           (cons
             "arguments"
             (list->vector (map Argument arg*)))
           (cons
             "result type"
             (Type type)))
         witness*)]
      [else witness*])
    (LedgerField : Program-Element (ir field*) -> * (json)
      (definitions
        (define (collect-bindings pl-array)
          (let f ([pl-array pl-array] [pb* '()])
            (nanopass-case (Lnodisclose Public-Ledger-Array) pl-array
              [(public-ledger-array ,pl-array-elt* ...)
               (fold-right
                 (lambda (elt pb*)
                   (nanopass-case (Lnodisclose Public-Ledger-Array-Element) elt
                     [,pl-array (f pl-array pb*)]
                     [,public-binding (cons public-binding pb*)]))
                 pb*
                 pl-array-elt*)])))
        (define (unwrap-alias type)
          (nanopass-case (Lnodisclose Type) type
            [(talias ,src ,nominal? ,type-name ,type) (unwrap-alias type)]
            [else type]))
        (define (serialize-binding pb)
          (nanopass-case (Lnodisclose Public-Ledger-Binding) pb
            [(,src ,ledger-field-name (,path-index* ...) ,type)
             (let ([unwrapped (unwrap-alias type)])
               (nanopass-case (Lnodisclose Type) unwrapped
                 [(tadt ,src^ ,adt-name ([,adt-formal* ,adt-arg*] ...) ,vm-expr (,adt-op* ...) (,adt-rt-op* ...))
                  (let ([clean-name (clean-adt-name adt-name)])
                    (append
                      (list
                        (cons "name" (symbol->string (id-sym ledger-field-name)))
                        (cons "index"
                          (if (= (length path-index*) 1)
                              (car path-index*)
                              (list->vector path-index*)))
                        (cons "exported" (id-exported? ledger-field-name))
                        (cons "storage" (adt-name->storage clean-name)))
                      (adt-type-fields clean-name adt-arg* Type)))]
                 [else
                  (internal-errorf 'save-contract-info
                    "ledger field ~a: type after alias unwrapping is not an ADT"
                    (symbol->string (id-sym ledger-field-name)))]))])))
      [(public-ledger-declaration ,pl-array ,lconstructor)
       (fold-right
         (lambda (pb field*) (cons (serialize-binding pb) field*))
         field*
         (collect-bindings pl-array))]
      [else field*])
    (exported-circuit : Program-Element (ir circuit* export-alist) -> * (json)
      (definitions
        (define (external-names id)
          (fold-right
            (lambda (a external-name*)
              (if (eq? (cdr a) id)
                  (cons (symbol->string (car a)) external-name*)
                  external-name*))
            '()
            export-alist)))
      [(circuit ,src ,function-name (,arg* ...) ,type ,expr)
       (guard (id-exported? function-name))
       (fold-right
         (lambda (external-name circuit*)
           (cons
             (list
               (cons
                 "name"
                 external-name)
               (cons
                 "pure"
                 (id-pure? function-name))
               (cons
                 "proof"
                 (and (memq (id-sym function-name) proof-circuit-name*) #t))
               (cons
                 "arguments"
                 (list->vector (map Argument arg*)))
               (cons
                 "result-type"
                 (Type type)))
             circuit*))
         circuit*
         (external-names function-name))]
      [else circuit*])
    (Argument : Argument (ir) -> * (json)
      [(,var-name ,type)
       (list
         (cons
           "name"
           (symbol->string (id-sym var-name)))
         (cons
           "type"
           (Type type)))])
    (Type : Type (ir) -> * (datum)
      [(tboolean ,src)
       (list
         (cons "type-name" "Boolean"))]
      [(tfield ,src)
       (list
         (cons "type-name" "Field"))]
      [(tunsigned ,src ,nat)
       (list
         (cons "type-name" "Uint")
         (cons "maxval" nat))]
      [(tbytes ,src ,len)
       (list
         (cons "type-name" "Bytes")
         (cons "length" len))]
      [(topaque ,src ,opaque-type)
       (list
         (cons "type-name" "Opaque")
         (cons "tsType" opaque-type))]
      [(tvector ,src ,len ,type)
       (list
         (cons "type-name" "Vector")
         (cons "length" len)
         (cons "type" (Type type)))]
      [(tcontract ,src ,contract-name (,elt-name* ,pure-dcl* (,type** ...) ,type*) ...)
       (list
         (cons "type-name" "Contract")
         (cons "name" (symbol->string contract-name))
         (cons
           "circuits"
           (list->vector
             (map (lambda (elt-name pure-dcl type* type)
                    (list
                      (cons "name" (symbol->string elt-name))
                      (cons "pure" pure-dcl)
                      (cons
                        "argument-types"
                        (list->vector (map Type type*)))
                      (cons "result-type" (Type type))))
                  elt-name* pure-dcl* type** type*))))]
      [(ttuple ,src ,type* ...)
       (list
         (cons "type-name" "Tuple")
         (cons "types" (list->vector (map Type type*))))]
      [(tstruct ,src ,struct-name (,elt-name* ,type*) ...)
       (list
         (cons "type-name" "Struct")
         (cons "name" (symbol->string struct-name))
         (cons
           "elements"
           (list->vector
             (map (lambda (elt-name type)
                    (list
                      (cons "name" (symbol->string elt-name))
                      (cons "type" (Type type))))
                  elt-name* type*))))]
      [(tenum ,src ,enum-name ,elt-name ,elt-name* ...)
       (list
         (cons "type-name" "Enum")
         (cons "name" (symbol->string enum-name))
         (cons
           "elements"
           (list->vector (map symbol->string (cons elt-name elt-name*)))))]
      [(tadt ,src ,adt-name ([,adt-formal* ,adt-arg*] ...) ,vm-expr (,adt-op* ...) (,adt-rt-op* ...))
       (let ([clean-name (clean-adt-name adt-name)])
         (cons (cons "type-name" clean-name)
               (adt-type-fields clean-name adt-arg* Type)))]
      [(talias ,src ,nominal? ,type-name ,type)
       (if nominal?
           (list
             (cons "type-name" "Alias")
             (cons "name" (symbol->string type-name))
             (cons "type" (Type type)))
           (Type type))]
      [else (assert cannot-happen)]))

  (define-passes save-contract-info-passes
    (save-contract-info              Lnodisclose))
)
