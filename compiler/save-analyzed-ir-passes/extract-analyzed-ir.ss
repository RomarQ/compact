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

#!chezscheme

(define-pass extract-analyzed-ir : Lloweredemit (ir proof-circuit-name*) -> Lanalyzed ()
  (definitions
    (define (fail what x) (internal-errorf 'save-analyzed-ir "unsupported ~a: ~s" what x))

    (define (native-type-argument* native-entry arg* type)
      (let ([seen (make-hashtable symbol-hash eq?)])
        (fold-right
          (lambda (maybe-type-param type acc)
            (if (and maybe-type-param (not (hashtable-contains? seen maybe-type-param)))
                (begin
                  (hashtable-set! seen maybe-type-param #t)
                  (cons (Type type) acc))
                acc))
          '()
          (native-entry-maybe-type-param* native-entry)
          (append (map (lambda (arg)
                         (nanopass-case (Lloweredemit Argument) arg
                           [(,var-name ,type) type]))
                       arg*)
                  (list type)))))

    (define (render-type type) (unparse-Lanalyzed (Type type)))
    (define (render-expr expr) (unparse-Lanalyzed (Expr expr)))

    (define (rendered? value) (and (pair? value) (symbol? (car value))))

    (define (vm-value->sexp value)
      (cond
        [(or (integer? value) (boolean? value) (string? value)) value]
        [(and (pair? value) (not (rendered? value))) (map vm-value->sexp value)]
        [(rendered? value) value]
        [(null? value) '()]
        [(VMop? value)
         (VMop-case value
           [(VMstack) '(stack)]
           [(VMvoid) '(void)]
           [(VMalign value bytes) `(align ,value ,bytes)]
           [(VM+ x y) `(+ ,(vm-value->sexp x) ,(vm-value->sexp y))]
           [(VMvalue->int x) `(value->int ,(vm-value->sexp x))]
           [(VMnull x) `(null ,(render-type x))]
           [(VMmax-sizeof x) `(max-sizeof ,(render-type x))]
           [(VMleaf-hash x) `(leaf-hash ,(vm-value->sexp x))]
           [(VMcoin-commit coin recipient)
            `(coin-commit ,(vm-value->sexp coin) ,(vm-value->sexp recipient))]
           [(VMaligned-concat value*) `(aligned-concat ,@(map vm-value->sexp value*))]
           [(VMstate-value-null) '(state-value null)]
           [(VMstate-value-cell value) `(state-value cell ,(vm-value->sexp value))]
           [(VMstate-value-ADT value type)
            `(state-value ADT ,(vm-value->sexp value) ,(render-type type))]
           [(VMstate-value-array value*) `(state-value array ,@(map vm-value->sexp value*))]
           [(VMstate-value-map key* value*)
            `(state-value map ,@(map (lambda (key value) `(,(vm-value->sexp key) ,(vm-value->sexp value))) key* value*))]
           [(VMstate-value-merkle-tree nat key* value*)
            `(state-value merkle-tree ,nat
               ,@(map (lambda (key value) `(,(vm-value->sexp key) ,(vm-value->sexp value))) key* value*))]
           [else (fail "VM value" value)])]
        [else (render-expr value)]))

    (define (vm-suppressed? value)
      (and (VMop? value) (VMop-case value [(VMsuppress) #t] [else #f])))

    (define (vminstr->sexp instruction)
      (let ([arg* (vminstr-arg* instruction)])
        (if (ormap (lambda (arg) (vm-suppressed? (cdr arg))) arg*)
            #f
            (let ([rendered
                   `(,(string->symbol (vminstr-op instruction))
                     ,@(map (lambda (arg) `(,(string->symbol (car arg)) ,(vm-value->sexp (cdr arg)))) arg*))])
              (if (and (eq? (car rendered) 'ins)
                       (member '(n (void)) (cdr rendered)))
                  #f
                  rendered)))))

    (define (instructions->sexp instruction*)
      (fold-right
        (lambda (instruction acc) (let ([sexp (vminstr->sexp instruction)]) (if sexp (cons sexp acc) acc)))
        '()
        instruction*))

    (define (expand-ops src path-elt* adt-formal* adt-arg* var-name* expr* vm-code)
      (instructions->sexp
        (expand-vm-code src
          (map (lambda (path-elt)
                 (nanopass-case (Lloweredemit Path-Element) path-elt
                   [,path-index (VMalign path-index 1)]
                   [(,src ,type ,expr) (render-expr expr)]))
               path-elt*)
          #f
          (append (map cons adt-formal* adt-arg*)
                  (map (lambda (var-name expr) (cons (id-sym var-name) (render-expr expr))) var-name* expr*))
          (vm-code-code vm-code))))

    (define (expand-emit src event-version event-tag expr vm-code)
      (instructions->sexp
        (expand-vm-code src #f #f
          (list (cons 'emit-version event-version)
                (cons 'emit-tag event-tag)
                (cons 'emit-payload (unparse-Lanalyzed expr)))
          (vm-code-code vm-code)))))

  (Type : Type (type) -> Type ())

  (Argument : Argument (arg) -> Argument ())

  (Path-Element : Path-Element (path-elt) -> Path-Element ())

  (ADT-Op-Class : ADT-Op-Class (op-class) -> ADT-Op-Class ())

  (Expr : Expression (expr) -> Expression ()
    [(emit ,src ,event-version ,event-tag ,len ,[expr] ,vm-code)
     `(emit ,src ,event-version ,event-tag ,len ,expr
        (,(expand-emit src event-version event-tag expr vm-code) ...))]
    [(public-ledger ,src ,ledger-field-name ,sugar (,path-elt* ...) ,src^ ,adt-op ,expr* ...)
     (nanopass-case (Lloweredemit ADT-Op) adt-op
       [(,ledger-op ,op-class (,adt-name (,adt-formal* ,adt-arg*) ...)
          ((,var-name* ,type*) ...) ,type ,vm-code)
        `(public-ledger ,src ,ledger-field-name ,(ADT-Op-Class op-class)
           (,(map Path-Element path-elt*) ...) ,ledger-op ,(Type type)
           (,(expand-ops src path-elt* adt-formal* adt-arg* var-name* expr* vm-code) ...)
           ,(map Expr expr*) ...)])])

  (Pelt : Program-Element (pelt proof-id*) -> Program-Element ()
    [(circuit ,src ,function-name (,arg* ...) ,type ,expr)
     `(circuit ,src ,function-name
        ,(id-exported? function-name)
        ,(id-pure? function-name)
        ,(and (memq function-name proof-id*) #t)
        (,(map Argument arg*) ...)
        ,(Type type)
        ,(Expr expr))]
    [(native ,src ,function-name ,native-entry (,arg* ...) ,type)
     `(native ,src ,function-name
        ,(native-entry-function native-entry)
        ,(native-entry-class native-entry)
        (,(native-type-argument* native-entry arg* type) ...)
        (,(map Argument arg*) ...)
        ,(Type type))])

  (Public-Ledger-Binding
    : Public-Ledger-Binding (binding) -> Public-Ledger-Binding ()
    [(,src ,ledger-field-name (,path-index* ...) ,[type])
     `(,src ,ledger-field-name (,path-index* ...)
        ,(id-exported? ledger-field-name)
        ,type)])

  (Program : Program (ir) -> Program ()
    [(program ,src (,contract-type* ...)
       ((,export-name* ,name*) ...) ,pelt* ...)
     (let* ([proof-id*
             (fold-left
               (lambda (acc export-name name)
                 (if (memq export-name proof-circuit-name*)
                     (cons name acc)
                     acc))
               '()
               export-name*
               name*)]
            [export* (map cons export-name* name*)])
       `(analyzed-ir
          ,compiler-version-string
          ,language-version-string
          ,runtime-version-string
          (,export* ...)
          (,(map Type contract-type*) ...)
          ,(map (lambda (pelt) (Pelt pelt proof-id*)) pelt*) ...))])

  (Program ir))
