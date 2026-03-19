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

  ;; Flatten a Public-Ledger-Array tree into a list of Public-Ledger-Binding nodes.
  ;; The pl-array is a B-tree (for >15 fields) that we flatten to a simple list.
  (define (flatten-pl-array pl-array)
    (nanopass-case (Lnodisclose Public-Ledger-Array) pl-array
      [(public-ledger-array ,pl-array-elt* ...)
       (apply append (map flatten-pl-array-elt pl-array-elt*))]))

  (define (flatten-pl-array-elt elt)
    (nanopass-case (Lnodisclose Public-Ledger-Array-Element) elt
      [,pl-array (flatten-pl-array pl-array)]
      [,public-binding (list public-binding)]))

  ;; Strip the __compact_ prefix from an ADT name if present and return a clean symbol.
  ;; In the IR, the Cell ADT is renamed to __compact_Cell by analysis-passes.ss.
  ;; Other ADTs (Map, Set, Counter, etc.) keep their original names.
  (define (clean-adt-name adt-name)
    (let ([s (symbol->string adt-name)])
      (if (and (> (string-length s) 10)
               (string=? (substring s 0 10) "__compact_"))
          (string->symbol (substring s 10 (string-length s)))
          adt-name)))

  ;; Map an ADT name (possibly __compact_-prefixed) to a canonical storage kind string
  ;; and a dispatch category symbol for serialize-ledger-adt.
  ;; Returns (values storage-string category-symbol).
  (define (classify-adt adt-name)
    (let ([cleaned (clean-adt-name adt-name)])
      (case cleaned
        [(Cell)                   (values "cell" 'cell)]
        [(Counter)                (values "counter" 'counter)]
        [(Map)                    (values "map" 'map)]
        [(Set)                    (values "set" 'element)]
        [(List)                   (values "list" 'element)]
        [(MerkleTree)             (values "merkle-tree" 'merkle-tree)]
        [(HistoricMerkleTree)     (values "historic-merkle-tree" 'merkle-tree)]
        [else                     (values (string-downcase (symbol->string cleaned)) 'unknown)])))

  ;; Helper: extract an ADT-Arg as a JSON value via the Type transformer.
  (define (adt-arg->json arg Type)
    (nanopass-case (Lnodisclose Public-Ledger-ADT-Arg) arg
      [,type (Type type)]
      [,nat nat]))

  ;; Serialize a tadt (ledger ADT) type to a JSON alist with storage kind and inner types.
  ;; Returns a list of (key . value) pairs to splice into the ledger field entry.
  (define (serialize-ledger-adt adt-name adt-formal* adt-arg* Type)
    (let-values ([(storage category) (classify-adt adt-name)])
      (case category
        [(cell)
         ;; Cell has one type arg: the value type
         (list
           (cons "storage" storage)
           (cons "type" (adt-arg->json (car adt-arg*) Type)))]
        [(counter)
         ;; Counter has no type args; always Uint<128> (defined in midnight-ledger.ss)
         (list
           (cons "storage" storage)
           (cons "type"
             (list
               (cons "type-name" "Uint")
               (cons "maxval" (- (expt 2 128) 1)))))]
        [(map)
         ;; Map has two args: key type, value type
         (list
           (cons "storage" storage)
           (cons "key-type" (adt-arg->json (car adt-arg*) Type))
           (cons "value-type" (adt-arg->json (cadr adt-arg*) Type)))]
        [(element)
         ;; Set and List both have one type arg: element type
         (list
           (cons "storage" storage)
           (cons "element-type" (adt-arg->json (car adt-arg*) Type)))]
        [(merkle-tree)
         ;; MerkleTree/HistoricMerkleTree: first arg is depth (nat), second is element type
         (list
           (cons "storage" storage)
           (cons "depth" (adt-arg->json (car adt-arg*) Type))
           (cons "element-type" (adt-arg->json (cadr adt-arg*) Type)))]
        [else
         ;; Unknown ADT — emit storage name only
         (list (cons "storage" storage))])))

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
      [(public-ledger-declaration ,pl-array ,lconstructor)
       (let ([bindings (filter
                         (lambda (pb)
                           (nanopass-case (Lnodisclose Public-Ledger-Binding) pb
                             [(,src ,ledger-field-name (,path-index* ...) ,type)
                              (id-exported? ledger-field-name)]))
                         (flatten-pl-array pl-array))])
         (append
           (map
             (lambda (pb)
               (nanopass-case (Lnodisclose Public-Ledger-Binding) pb
                 [(,src ,ledger-field-name (,path-index* ...) ,type)
                  (let ([name (symbol->string (id-sym ledger-field-name))]
                        [index (if (= (length path-index*) 1) (car path-index*) (list->vector path-index*))])
                    ;; Unwrap alias to get to the tadt node
                    (let loop ([t type])
                      (nanopass-case (Lnodisclose Type) t
                        [(talias ,src ,nominal? ,type-name ,type)
                         (loop type)]
                        [(tadt ,src ,adt-name ([,adt-formal* ,adt-arg*] ...) ,vm-expr (,adt-op* ...) (,adt-rt-op* ...))
                         (append
                           (list
                             (cons "name" name)
                             (cons "index" index))
                           (serialize-ledger-adt adt-name adt-formal* adt-arg* Type))]
                        [else
                         ;; Non-ADT type -- unexpected for ledger fields, handle gracefully
                         (list
                           (cons "name" name)
                           (cons "index" index)
                           (cons "storage" "unknown")
                           (cons "type" (Type t)))])))]))
             bindings)
           field*))]
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
      [(talias ,src ,nominal? ,type-name ,type)
       (if nominal?
           (list
             (cons "type-name" "Alias")
             (cons "name" (symbol->string type-name))
             (cons "type" (Type type)))
           (Type type))]
      [(tadt ,src ,adt-name ([,adt-formal* ,adt-arg*] ...) ,vm-expr (,adt-op* ...) (,adt-rt-op* ...))
       ;; ADT types appear as inner types of Map/List values (e.g., Map<Field, MerkleTree<10, T>>).
       ;; Emit the storage kind as the type-name so consumers see "MerkleTree", "Map", etc.
       (let-values ([(storage _) (classify-adt adt-name)])
         (cons
           (cons "type-name" storage)
           (serialize-ledger-adt adt-name adt-formal* adt-arg* Type)))]
      [else (assert cannot-happen)]))

  (define-passes save-contract-info-passes
    (save-contract-info              Lnodisclose))
)
