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

  ; NB: must come after identify-pure-circuits
  (define-pass save-contract-info : Lnodisclose (ir proof-circuit-name*) -> Lnodisclose ()
    (definitions
      ; Collect all Public-Ledger-Bindings from a Public-Ledger-Array, flattening nested arrays
      (define (collect-pl-array pl-array)
        (nanopass-case (Lnodisclose Public-Ledger-Array) pl-array
          [(public-ledger-array ,pl-array-elt* ...)
           (fold-right
             (lambda (elt acc)
               (nanopass-case (Lnodisclose Public-Ledger-Array-Element) elt
                 [,pl-array^ (append (collect-pl-array pl-array^) acc)]
                 [,public-binding (cons (ledger-binding-json public-binding) acc)]))
             '()
             pl-array-elt*)]))
      ; Convert a Public-Ledger-Binding to a JSON object (list of key-value pairs)
      (define (ledger-binding-json public-binding)
        (nanopass-case (Lnodisclose Public-Ledger-Binding) public-binding
          [(,src ,ledger-field-name (,path-index* ...) ,type)
           (cons*
             (cons "name" (symbol->string (id-sym ledger-field-name)))
             (cons "index" (car path-index*))
             (tadt-storage-json type))]))
      ; Convert a tadt type to a list of key-value pairs describing its storage kind and type args
      (define (tadt-storage-json type)
        (nanopass-case (Lnodisclose Type) type
          [(talias ,src ,nominal? ,type-name ,inner-type)
           (tadt-storage-json inner-type)]
          [(tadt ,src ,adt-name ([,adt-formal* ,adt-arg*] ...) ,vm-expr (,adt-op* ...) (,adt-rt-op* ...))
           (case adt-name
             [(__compact_Cell)
              (list
                (cons "storage" "cell")
                (cons "type" (adt-arg-json (car adt-arg*))))]
             [(Counter)
              (list
                (cons "storage" "counter"))]
             [(Set)
              (list
                (cons "storage" "set")
                (cons "element-type" (adt-arg-json (car adt-arg*))))]
             [(Map)
              (list
                (cons "storage" "map")
                (cons "key-type" (adt-arg-json (car adt-arg*)))
                (cons "value-type" (adt-arg-json (cadr adt-arg*))))]
             [(MerkleTree)
              (list
                (cons "storage" "merkle-tree")
                (cons "depth" (adt-arg-json (car adt-arg*)))
                (cons "type" (adt-arg-json (cadr adt-arg*))))]
             [else
              (list
                (cons "storage" (string-downcase (symbol->string adt-name))))])]
          [else (assert cannot-happen)]))
      ; Convert a Public-Ledger-ADT-Arg to a JSON value
      (define (adt-arg-json adt-arg)
        (nanopass-case (Lnodisclose Public-Ledger-ADT-Arg) adt-arg
          [,nat nat]
          [,type (adt-type-json type)]))
      ; Convert a type that may be a tadt (for nested ADTs) or a regular type to JSON
      (define (adt-type-json type)
        (nanopass-case (Lnodisclose Type) type
          [(talias ,src ,nominal? ,type-name ,inner-type)
           (if nominal?
               (list
                 (cons "type-name" "Alias")
                 (cons "name" (symbol->string type-name))
                 (cons "type" (adt-type-json inner-type)))
               (adt-type-json inner-type))]
          [(tadt ,src ,adt-name ([,adt-formal* ,adt-arg*] ...) ,vm-expr (,adt-op* ...) (,adt-rt-op* ...))
           (case adt-name
             [(__compact_Cell)
              (list
                (cons "storage" "cell")
                (cons "type" (adt-arg-json (car adt-arg*))))]
             [(Counter)
              (list
                (cons "storage" "counter"))]
             [(Set)
              (list
                (cons "storage" "set")
                (cons "element-type" (adt-arg-json (car adt-arg*))))]
             [(Map)
              (list
                (cons "storage" "map")
                (cons "key-type" (adt-arg-json (car adt-arg*)))
                (cons "value-type" (adt-arg-json (cadr adt-arg*))))]
             [(MerkleTree)
              (list
                (cons "storage" "merkle-tree")
                (cons "depth" (adt-arg-json (car adt-arg*)))
                (cons "type" (adt-arg-json (cadr adt-arg*))))]
             [else
              (list
                (cons "storage" (string-downcase (symbol->string adt-name))))])]
          [else (Type type)]))
      ; Collect ledger bindings from a list of program elements
      (define (collect-ledger pelt*)
        (fold-right
          (lambda (pelt acc)
            (nanopass-case (Lnodisclose Program-Element) pelt
              [(public-ledger-declaration ,pl-array ,lconstructor)
               (append (collect-pl-array pl-array) acc)]
              [else acc]))
          '()
          pelt*)))
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
               (list->vector (collect-ledger pelt*))))))
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
      [else (assert cannot-happen)]))

  (define-passes save-contract-info-passes
    (save-contract-info              Lnodisclose))
)
