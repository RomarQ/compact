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
          (pass-helpers)
          (vm))

  ;; NB: must come after identify-pure-circuits
  (define-pass save-contract-info : Lnodisclose (ir proof-circuit-name*) -> Lnodisclose ()
    (definitions
      ;; Flatten a Public-Ledger-Array B-tree into a list of Public-Ledger-Binding nodes.
      (define (flatten-pl-array pl-array)
        (nanopass-case (Lnodisclose Public-Ledger-Array) pl-array
          [(public-ledger-array ,pl-array-elt* ...)
           (apply append (map flatten-pl-array-elt pl-array-elt*))]))

      (define (flatten-pl-array-elt elt)
        (nanopass-case (Lnodisclose Public-Ledger-Array-Element) elt
          [,pl-array (flatten-pl-array pl-array)]
          [,public-binding (list public-binding)]))

      ;; Strip the __compact_ prefix from an ADT name if present and return the
      ;; clean name as a symbol.  In the IR, the Cell ADT is renamed to
      ;; __compact_Cell by analysis-passes.ss; other ADTs keep their names.
      (define (clean-adt-name adt-name)
        (let ([s (symbol->string adt-name)])
          (if (string-prefix? "__compact_" s)
              (string->symbol (substring s 10 (string-length s)))
              adt-name)))

      ;; Serialize a ledger ADT as a JSON alist with a leading key/name entry
      ;; followed by type-specific fields.
      (define (serialize-adt key adt-name adt-arg*)
        (let ([cleaned (clean-adt-name adt-name)])
          (cons
            (cons key (string-downcase (symbol->string cleaned)))
            (case cleaned
              [(Cell)
               (list (cons "type" (adt-arg->json (car adt-arg*))))]
              [(Counter)
               '()]
              [(Map)
               (list (cons "key" (adt-arg->json (car adt-arg*)))
                     (cons "value" (adt-arg->json (cadr adt-arg*))))]
              [(Set List)
               (list (cons "type" (adt-arg->json (car adt-arg*))))]
              [(MerkleTree HistoricMerkleTree)
               (list (cons "depth" (adt-arg->json (car adt-arg*)))
                     (cons "type" (adt-arg->json (cadr adt-arg*))))]
              [else (assert cannot-happen)]))))

      ;; Extract an ADT-Arg as a JSON value via the Type transformer.
      (define (adt-arg->json arg)
        (nanopass-case (Lnodisclose Public-Ledger-ADT-Arg) arg
          [,type (Type type)]
          [,nat nat]))

      ;; Unwrap aliases to reach the underlying tadt node for a ledger field.
      (define (unwrap-to-adt type)
        (nanopass-case (Lnodisclose Type) type
          [(talias ,src ,nominal? ,type-name ,type)
           (unwrap-to-adt type)]
          [else type]))

      ;; ---------------------------------------------------------------
      ;; Circuit IR emitter — converts Lnodisclose Expression trees
      ;; into portable JSON IR for the "ir" field per circuit.
      ;; ---------------------------------------------------------------

      ;; Serialize a type to the IR JSON format.
      (define (ir-type->json type)
        (nanopass-case (Lnodisclose Type) type
          [(tboolean ,src)     (list (cons "type" "Boolean"))]
          [(tfield ,src)       (list (cons "type" "Field"))]
          [(tunsigned ,src ,nat)
           (list (cons "type" "Uint") (cons "maxval" (number->string nat)))]
          [(tbytes ,src ,len)
           (list (cons "type" "Bytes") (cons "length" len))]
          [(topaque ,src ,opaque-type)
           (list (cons "type" "Opaque") (cons "name" opaque-type))]
          [(tvector ,src ,len ,type)
           (list (cons "type" "Vector") (cons "length" len) (cons "element" (ir-type->json type)))]
          [(ttuple ,src ,type* ...)
           (list (cons "type" "Tuple") (cons "types" (list->vector (map ir-type->json type*))))]
          [(tstruct ,src ,struct-name (,elt-name* ,type*) ...)
           (list (cons "type" "Struct") (cons "name" (symbol->string struct-name)))]
          [(tenum ,src ,enum-name ,elt-name ,elt-name* ...)
           (list (cons "type" "Enum") (cons "name" (symbol->string enum-name)))]
          [(talias ,src ,nominal? ,type-name ,type) (ir-type->json type)]
          [else (list (cons "type" "Void"))]))

      ;; Convert a VMop value to JSON-safe form.
      (define (vmop->json v)
        (cond
          [(integer? v) v]
          [(boolean? v) v]
          [(string? v) v]
          [(list? v) (list->vector (map vmop->json v))]
          [(VMop? v)
           (VMop-case v
             [(VMstack) "stack"]
             [(VMvoid) (void)]
             [(VMsuppress) (void)]
             [(VMalign value bytes)
              (list (cons "tag" "value")
                    (cons "value" (number->string value))
                    (cons "type" (list (cons "type" "Uint")
                                       (cons "maxval" (number->string (- (expt 2 (* bytes 8)) 1))))))]
             [(VMvalue->int x) (vmop->json x)]
             [(VMstate-value-cell val) (vmop->json val)]
             [(VMstate-value-null) (void)]
             [else (format "~s" v)])]
          [else
           (guard (c [#t (format "~s" v)])
             (emit-ir-expr v))]))

      ;; Convert a vminstr to IR LedgerOp JSON.
      (define (vminstr->ir-json vi)
        (let ([op (vminstr-op vi)] [args (vminstr-arg* vi)])
          (define (get-arg name) (cdr (assoc name args)))
          (define (has-arg? name) (assoc name args))
          (cond
            [(string=? op "idx")
             (let ([cached (get-arg "cached")]
                   [push-path (get-arg "pushPath")]
                   [path (get-arg "path")])
               (list (cons "op" "idx")
                     (cons "cached" (if cached #t #f))
                     (cons "push-path" (if push-path #t #f))
                     (cons "path" (list->vector
                                    (map (lambda (p)
                                           (let ([v (vmop->json p)])
                                             (if (and (list? v) (assoc "tag" v))
                                                 v
                                                 (list (cons "tag" "value")
                                                       (cons "value" (format "~a" v))
                                                       (cons "type" (list (cons "type" "Uint") (cons "maxval" "255")))))))
                                         path)))))]
            [(string=? op "addi")
             (list (cons "op" "addi")
                   (cons "immediate" (vmop->json (get-arg "immediate"))))]
            [(string=? op "ins")
             (let ([n-val (vmop->json (get-arg "n"))])
               ;; Skip suppressed ins (n = void/null)
               (if (or (eq? n-val (void)) (not (integer? n-val)))
                   (error 'vminstr->ir-json "suppressed ins op")
                   (list (cons "op" "ins")
                         (cons "cached" (if (get-arg "cached") #t #f))
                         (cons "n" n-val))))]
            [(string=? op "dup")     (list (cons "op" "dup"))]
            [(string=? op "popeq")   (list (cons "op" "popeq"))]
            [(string=? op "member")  (list (cons "op" "member"))]
            [(string=? op "root")    (list (cons "op" "root"))]
            [(string=? op "eq")      (list (cons "op" "eq"))]
            [(string=? op "ckpt")    (list (cons "op" "ckpt"))]
            [(string=? op "push")
             (let ([storage (if (has-arg? "storage") (get-arg "storage") #f)]
                   [value (get-arg "value")])
               (list (cons "op" "push")
                     (cons "storage" (if storage #t #f))
                     (cons "value" (vmop->json value))))]
            [(string=? op "rem")
             (list (cons "op" "rem")
                   (cons "cached" (if (get-arg "cached") #t #f))
                   (cons "n" (vmop->json (get-arg "n"))))]
            [(string=? op "noop")
             (list (cons "op" "noop")
                   (cons "n" (if (has-arg? "n") (get-arg "n") 0)))]
            [else
             (cons (cons "op" op)
                   (map (lambda (a) (cons (car a) (vmop->json (cdr a)))) args))])))

      ;; Emit an expression as IR JSON.
      (define (emit-ir-expr expr)
        (nanopass-case (Lnodisclose Expression) expr
          [(var-ref ,src ,var-name)
           (list (cons "op" "var")
                 (cons "name" (symbol->string (id-sym var-name))))]
          [(quote ,src ,datum)
           (list (cons "op" "lit")
                 (cons "type" (list (cons "type" "Void")))
                 (cons "value" (format "~a" datum)))]
          [(assert ,src ,expr ,mesg)
           (list (cons "op" "assert")
                 (cons "expr" (emit-ir-expr expr))
                 (cons "message" mesg))]
          [(if ,src ,expr0 ,expr1 ,expr2)
           (list (cons "op" "if-expr")
                 (cons "cond" (emit-ir-expr expr0))
                 (cons "then" (emit-ir-expr expr1))
                 (cons "else" (emit-ir-expr expr2)))]
          [(+ ,src ,mbits ,expr1 ,expr2)
           (list (cons "op" "add")
                 (cons "left" (emit-ir-expr expr1))
                 (cons "right" (emit-ir-expr expr2)))]
          [(- ,src ,mbits ,expr1 ,expr2)
           (list (cons "op" "sub")
                 (cons "left" (emit-ir-expr expr1))
                 (cons "right" (emit-ir-expr expr2)))]
          [(* ,src ,mbits ,expr1 ,expr2)
           (list (cons "op" "mul")
                 (cons "left" (emit-ir-expr expr1))
                 (cons "right" (emit-ir-expr expr2)))]
          [(== ,src ,type ,expr1 ,expr2)
           (list (cons "op" "eq")
                 (cons "left" (emit-ir-expr expr1))
                 (cons "right" (emit-ir-expr expr2)))]
          [(< ,src ,mbits ,expr1 ,expr2)
           (list (cons "op" "lt")
                 (cons "left" (emit-ir-expr expr1))
                 (cons "right" (emit-ir-expr expr2)))]
          [(elt-ref ,src ,expr ,elt-name ,nat)
           (list (cons "op" "field")
                 (cons "expr" (emit-ir-expr expr))
                 (cons "name" (symbol->string elt-name)))]
          [(tuple-ref ,src ,expr ,kindex)
           (list (cons "op" "index")
                 (cons "expr" (emit-ir-expr expr))
                 (cons "index" kindex))]
          [(enum-ref ,src ,type ,elt-name)
           (list (cons "op" "lit")
                 (cons "type" (ir-type->json type))
                 (cons "value" (symbol->string elt-name)))]
          [(call ,src ,function-name ,expr* ...)
           (let ([name (symbol->string (id-sym function-name))])
             (list (cons "op" (if (id-pure? function-name) "call-pure" "call-witness"))
                   (cons "name" name)
                   (cons "args" (list->vector (map emit-ir-expr expr*)))
                   (cons "result-type" (list (cons "type" "Void")))))]
          [(let* ,src ([,local* ,expr*] ...) ,expr)
           (let ([let-stmts (map (lambda (loc bind-expr)
                                   (let ([name (nanopass-case (Lnodisclose Argument) loc
                                                 [(,var-name ,type)
                                                  (symbol->string (id-sym var-name))])])
                                     (list (cons "op" "let")
                                           (cons "name" name)
                                           (cons "value" (emit-ir-expr bind-expr)))))
                                 local* expr*)]
                 [body-expr (emit-ir-expr expr)])
             (if (null? let-stmts)
                 body-expr
                 (list (cons "op" "let-expr")
                       (cons "bindings" (list->vector let-stmts))
                       (cons "body" body-expr))))]
          [(public-ledger ,src ,ledger-field-name ,sugar (,path-elt* ...) ,src^ ,adt-op ,expr* ...)
           (nanopass-case (Lnodisclose ADT-Op) adt-op
             [(,ledger-op ,op-class (,adt-name (,adt-formal* ,adt-arg*) ...) ((,var-name* ,type*) ...) ,type ,vm-code)
              (let* ([path-vals (map (lambda (pe)
                                       (nanopass-case (Lnodisclose Path-Element) pe
                                         [,path-index (VMalign path-index 1)]
                                         [(,src ,type ,expr) (emit-ir-expr expr)]))
                                     path-elt*)]
                     [arg-alist (append
                                  (map (lambda (f a) (cons f a)) adt-formal* adt-arg*)
                                  (map (lambda (vn ex) (cons (id-sym vn) ex)) var-name* expr*))]
                     [result-type (ir-type->json type)]
                     [vminstr* (expand-vm-code src path-vals #f arg-alist (vm-code-code vm-code))]
                     [json-ops (fold-right
                                 (lambda (vi acc)
                                   (guard (c [#t acc])
                                     (cons (vminstr->ir-json vi) acc)))
                                 '()
                                 vminstr*)])
                (list (cons "op" "ledger-query")
                      (cons "ops" (list->vector json-ops))
                      (cons "result-type" result-type)))])]
          [(default ,src ,type)
           (list (cons "op" "default") (cons "type" (ir-type->json type)))]
          [(seq ,src ,expr* ... ,expr)
           (emit-ir-expr expr)]
          [(return ,src ,expr)
           (emit-ir-expr expr)]
          [(safe-cast ,src ,type ,type^ ,expr)
           (emit-ir-expr expr)]
          [(tuple ,src ,tuple-arg* ...)
           (list (cons "op" "lit")
                 (cons "type" (list (cons "type" "Tuple") (cons "types" (list->vector '()))))
                 (cons "value" ""))]
          [else
           (list (cons "op" "lit")
                 (cons "type" (list (cons "type" "Void")))
                 (cons "value" ""))]))

      ;; Emit a circuit body expression as a statement tree.
      (define (emit-ir-body the-expr)
        (nanopass-case (Lnodisclose Expression) the-expr
          [(seq ,src ,expr* ... ,expr)
           (let ([stmts (map (lambda (e)
                               (list (cons "op" "expr-stmt")
                                     (cons "expr" (emit-ir-expr e))))
                             (append expr* (list expr)))])
             (list (cons "op" "seq")
                   (cons "stmts" (list->vector stmts))))]
          [else
           (list (cons "op" "seq")
                 (cons "stmts" (list->vector
                                 (list (list (cons "op" "expr-stmt")
                                             (cons "expr" (emit-ir-expr the-expr)))))))])))

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
               (list->vector (fold-right LedgerField '() pelt*)))
             (cons
               "helpers"
               ;; Collect all internal circuit/function bodies as helpers.
               ;; These are pure functions referenced by impure circuits.
               (let ([helpers '()])
                 (for-each
                   (lambda (pelt)
                     (nanopass-case (Lnodisclose Program-Element) pelt
                       [(circuit ,src ,function-name (,arg* ...) ,type ,expr)
                        ;; Include all circuits as potential helpers
                        (let* ([name (symbol->string (id-sym function-name))]
                               [params (map (lambda (a)
                                              (nanopass-case (Lnodisclose Argument) a
                                                [(,var-name ,type)
                                                 (list (cons "name" (symbol->string (id-sym var-name)))
                                                       (cons "type" (ir-type->json type)))]))
                                            arg*)])
                          (set! helpers
                            (cons
                              (list (cons "name" name)
                                    (cons "params" (list->vector params))
                                    (cons "body" (emit-ir-body expr))
                                    (cons "result" (void)))
                              helpers)))]
                       [else (void)]))
                   pelt*)
                 (list->vector helpers))))))
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
       (let ([bindings (flatten-pl-array pl-array)])
         (append
           (map
             (lambda (pb)
               (nanopass-case (Lnodisclose Public-Ledger-Binding) pb
                 [(,src ,ledger-field-name (,path-index* ...) ,type)
                  (let ([name (symbol->string (id-sym ledger-field-name))]
                        [index (if (and (pair? path-index*) (null? (cdr path-index*))) (car path-index*) (list->vector path-index*))]
                        [exported (id-exported? ledger-field-name)]
                        [unwrapped (unwrap-to-adt type)])
                    (nanopass-case (Lnodisclose Type) unwrapped
                      [(tadt ,src ,adt-name ([,adt-formal* ,adt-arg*] ...) ,vm-expr (,adt-op* ...) (,adt-rt-op* ...))
                       (cons*
                         (cons "name" name)
                         (cons "index" index)
                         (cons "exported" exported)
                         (serialize-adt "storage" adt-name adt-arg*))]
                      [else (assert cannot-happen)]))]))
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
                 (Type type))
               (cons
                 "ir"
                 (if (and (not (id-pure? function-name))
                          (memq (id-sym function-name) proof-circuit-name*))
                     (list
                       (cons "body" (emit-ir-body expr))
                       (cons "result" (void)))
                     (void))))
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
       (serialize-adt "type-name" adt-name adt-arg*)]
      [else (assert cannot-happen)]))

  (define-passes save-contract-info-passes
    (save-contract-info              Lnodisclose))
)
