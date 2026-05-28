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

  ; NB: must come after identify-pure-circuits
  (define-pass save-contract-info : Lnodisclose (ir novectorref-ir proof-circuit-name*) -> Lnodisclose ()
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
            (cons key (symbol->string cleaned))
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
      ;; Pure function calls are inlined (like the TypeScript backend).
      ;; ---------------------------------------------------------------

      ;; Map circuit-name-symbol → lowered (Lnovectorref) body expression,
      ;; populated from the lowered circuit program. This is the source of each
      ;; circuit's `ir` field: the body with enums resolved, loops unrolled,
      ;; helpers inlined and safe-casts removed by circuit-passes.
      (define lowered-body-table (make-eq-hashtable))

      ;; Signature table: function-name-symbol → (class result-type)
      ;; where class is one of 'native-circuit, 'native-witness, 'witness-decl.
      ;; Populated from Lnodisclose Program-Element `native` and `witness`
      ;; declarations. Used by the `(call ...)` IR emitter to decide between
      ;; emitting `call-pure` (native circuit builtins like `transientHash`,
      ;; `ecMul`, `jubjubPointX`, ...) and `call-witness` (truly external
      ;; private-state callbacks), and to attach the correct result-type.
      (define signature-table (make-eq-hashtable))

      ;; Struct table: struct-name-symbol → vector of field JSON objects.
      ;; Populated as a side effect of `ir-type->json` walking struct types.
      ;; Each field is `{name, type}`. Emitted as a top-level `structs` array
      ;; in contract-info.json so the IR consumer can compute atom layouts
      ;; for Value::AlignedValue field slicing.
      (define struct-table (make-eq-hashtable))

      ;; Serialize a lowered (Lnovectorref) type to the IR JSON format.
      (define (ir-type->json type)
        (nanopass-case (Lnovectorref Type) type
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
           ;; Monomorphize parametric structs (e.g. `Maybe<T>`) so each
           ;; instantiation gets its own entry in `struct-table`. We key
           ;; on `(struct-name + field-type-fingerprint)` so structurally
           ;; identical instantiations dedupe but different ones don't
           ;; collide.
           ;;
           ;; The fingerprint is the string concatenation of each field
           ;; type's JSON, recursed via `ir-type->json`. For non-parametric
           ;; structs the fingerprint is constant across all references and
           ;; the original name wins; for parametric ones we suffix with a
           ;; per-fingerprint counter so the consumer sees distinct names
           ;; like `Maybe`, `Maybe_2`, etc.
           (let* ([base-name (symbol->string struct-name)]
                  [field-jsons (map (lambda (t) (ir-type->json t)) type*)]
                  [fingerprint
                   (let ([sp (open-output-string)])
                     (for-each
                       (lambda (n j)
                         (put-string sp (symbol->string n))
                         (put-string sp ":")
                         (put-string sp (format "~s" j))
                         (put-string sp ";"))
                       elt-name* field-jsons)
                     (get-output-string sp))]
                  [key (string->symbol (string-append base-name "$" fingerprint))]
                  [unique-name
                   (cond
                     [(hashtable-ref struct-table key #f) =>
                      (lambda (entry) (car entry))]
                     [else
                      ;; First time we see this fingerprint — pick a name
                      ;; that doesn't collide with any other already-named
                      ;; struct with a different fingerprint.
                      (let loop ([candidate base-name] [n 1])
                        (let ([taken? #f])
                          (let-values ([(keys vals) (hashtable-entries struct-table)])
                            (vector-for-each
                              (lambda (v)
                                (when (and (pair? v)
                                           (string=? (car v) candidate))
                                  (set! taken? #t)))
                              vals))
                          (if taken?
                              (loop (string-append base-name "_" (number->string (+ n 1))) (+ n 1))
                              candidate)))])])
             (unless (hashtable-contains? struct-table key)
               ;; Insert placeholder first to break recursion through
               ;; nested struct fields that may reference this same type.
               (hashtable-set! struct-table key (list unique-name #f))
               (let ([fields (map (lambda (n j)
                                    (list (cons "name" (symbol->string n))
                                          (cons "type" j)))
                                  elt-name* field-jsons)])
                 (hashtable-set! struct-table key (list unique-name (list->vector fields)))))
             (list (cons "type" "Struct") (cons "name" unique-name)))]
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
             [(VMstate-value-ADT val type)
              ;; A cell containing a structured (struct/tuple/etc) value.
              ;; We don't have the static type information needed to encode
              ;; the inner value at this layer, so emit it as an `expr`
              ;; reference that the consumer evaluates at runtime. The val
              ;; is typically an Lnodisclose Expression (e.g. a var-ref to
              ;; a let-bound struct literal).
              (vmop->json val)]
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
            [(string=? op "popeq")
             (list (cons "op" "popeq")
                   (cons "cached" (if (has-arg? "cached")
                                      (if (get-arg "cached") #t #f)
                                      #f)))]
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


      ;; Emit a lowered (Lnovectorref) expression as IR JSON. Enums, map/fold,
      ;; helper calls and safe-casts are already lowered away by circuit-passes,
      ;; so this only handles the post-lowering expression forms.
      (define (emit-ir-expr expr)
        (nanopass-case (Lnovectorref Expression) expr
          [(var-ref ,src ,var-name)
           (list (cons "op" "var")
                 (cons "name" (symbol->string (id-sym var-name))))]
          [(quote ,src ,datum)
           ;; Emit a typed literal so the IR consumer can decode it.
           ;; `(quote)` datums in Lnodisclose are produced by `lparser-to-lsrc`
           ;; for boolean (`#t`/`#f`), field-element (integer), and
           ;; byte-string (bytevector, from `string` / `pad`) source forms.
           (cond
             [(boolean? datum)
              (list (cons "op" "lit")
                    (cons "type" (list (cons "type" "Boolean")))
                    (cons "value" (if datum "true" "false")))]
             [(integer? datum)
              (list (cons "op" "lit")
                    (cons "type" (list (cons "type" "Field")))
                    (cons "value" (number->string datum)))]
             [(bytevector? datum)
              (let ([len (bytevector-length datum)])
                (list (cons "op" "lit")
                      (cons "type" (list (cons "type" "Bytes")
                                         (cons "length" len)))
                      ;; Hex-encoded big-endian bytes (no `0x` prefix). The
                      ;; consumer parses this back into a `[u8; length]`.
                      (cons "value"
                            (apply string-append
                                   (map (lambda (b)
                                          (let ([s (number->string b 16)])
                                            (if (< b 16)
                                                (string-append "0" s)
                                                s)))
                                        (bytevector->u8-list datum))))))]
             [else
              ;; Unknown datum shape — fall back to Void so the consumer
              ;; can at least see something, but this is a compiler bug.
              (list (cons "op" "lit")
                    (cons "type" (list (cons "type" "Void")))
                    (cons "value" (format "~a" datum)))])]
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
          [(< ,src ,bits ,expr1 ,expr2)
           (list (cons "op" "lt")
                 (cons "left" (emit-ir-expr expr1))
                 (cons "right" (emit-ir-expr expr2)))]
          [(elt-ref ,src ,expr ,elt-name)
           (list (cons "op" "field")
                 (cons "expr" (emit-ir-expr expr))
                 (cons "name" (symbol->string elt-name)))]
          [(tuple-ref ,src ,expr ,kindex)
           (list (cons "op" "index")
                 (cons "expr" (emit-ir-expr expr))
                 (cons "index" kindex))]
          [(bytes-ref ,src ,expr ,nat)
           ;; Byte access `expr[nat]` on a Bytes value at constant index `nat`.
           (list (cons "op" "index")
                 (cons "expr" (emit-ir-expr expr))
                 (cons "index" nat))]
          [(call ,src ,function-name ,expr* ...)
           (let* ([name (symbol->string (id-sym function-name))]
                  [fn-sym (id-sym function-name)]
                  [json-args (list->vector (map emit-ir-expr expr*))])
             (cond
               ;; Native builtin or witness declaration: dispatch by class.
               ;; (User-defined helper circuits are inlined away by this stage.)
               [(hashtable-contains? signature-table fn-sym)
                (let* ([sig (hashtable-ref signature-table fn-sym #f)]
                       [cls (car sig)]
                       [result-type (cadr sig)])
                  (case cls
                    [(native-circuit)
                     ;; Pure builtin (transientHash, ecMul, ...). Emit
                     ;; call-pure so the interpreter resolves it via
                     ;; try_builtin.
                     (list (cons "op" "call-pure")
                           (cons "name" name)
                           (cons "args" json-args)
                           (cons "result-type" (ir-type->json result-type)))]
                    [else
                     ;; native-witness or user witness declaration:
                     ;; private-state callback. Emit call-witness with
                     ;; real args and the declared result type.
                     (list (cons "op" "call-witness")
                           (cons "name" name)
                           (cons "args" json-args)
                           (cons "result-type" (ir-type->json result-type)))]))]
               [else
                ;; Last resort: unknown function. Emit a Void-typed
                ;; call-witness so the consumer at least sees the call.
                (fprintf (current-error-port)
                         "save-contract-info: unknown function ~a, emitting Void call-witness~n"
                         name)
                (list (cons "op" "call-witness")
                      (cons "name" name)
                      (cons "args" json-args)
                      (cons "result-type" (list (cons "type" "Void"))))]))]
          [(let* ,src ([,local* ,expr*] ...) ,expr)
           (let ([let-stmts (map (lambda (loc bind-expr)
                                   (let ([name (nanopass-case (Lnovectorref Argument) loc
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
           (nanopass-case (Lnovectorref ADT-Op) adt-op
             [(,ledger-op ,op-class (,adt-name (,adt-formal* ,adt-arg*) ...) ((,var-name* ,type*) ...) ,type ,vm-code)
              (let* ([path-vals (map (lambda (pe)
                                       (nanopass-case (Lnovectorref Path-Element) pe
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
           ;; Lower a seq in expression position to a let-expr chain so the
           ;; consumer (which only understands let-expr in expression
           ;; position) sees every sub-expression in source order. Each
           ;; non-final expression is bound to a fresh discard name; the
           ;; final expression becomes the body.
           (let loop ([rest expr*] [n 0])
             (if (null? rest)
                 (emit-ir-expr expr)
                 (list (cons "op" "let-expr")
                       (cons "bindings"
                             (list->vector
                               (list (list (cons "op" "let")
                                           (cons "name" (format "__seq_~a" n))
                                           (cons "value" (emit-ir-expr (car rest)))))))
                       (cons "body" (loop (cdr rest) (+ n 1))))))]
          [(new ,src ,type ,expr* ...)
           ;; Struct literal: `StructName { field0: e0, field1: e1, ... }`.
           ;; Emit a `new` op carrying the struct's TypeRef and the field
           ;; expressions in declaration order. The interpreter uses the
           ;; type to look up the struct layout and encode each element
           ;; with the correct per-field alignment — necessary so that
           ;; e.g. `amount: Uint<128>` encodes as 16 bytes, not the 8 bytes
           ;; that `Value::Integer` would default to.
           (list (cons "op" "new")
                 (cons "type" (ir-type->json type))
                 (cons "elements"
                       (list->vector (map emit-ir-expr expr*))))]
          [(downcast-unsigned ,src ,nat? ,nat ,expr)
           ;; `expr as Uint<maxval>` — narrowing cast. `nat` is the target
           ;; type's `maxval`, not its bit width (see circuit-passes.ss:57).
           ;; `nat?` is the optional secondary bound added upstream; unused here.
           ;; Ship as a `cast` op; the consumer passes the inner value
           ;; through unchanged at runtime. We don't have the source type
           ;; here, so use a generous Field for `from`.
           (list (cons "op" "cast")
                 (cons "expr" (emit-ir-expr expr))
                 (cons "from" (list (cons "type" "Field")))
                 (cons "to" (list (cons "type" "Uint")
                                  (cons "maxval" (number->string nat)))))]
          [(tuple ,src ,tuple-arg* ...)
           ;; An empty tuple is the Compact unit value; emit a Void lit so the
           ;; consumer treats it as Value::Void. A non-empty tuple becomes a
           ;; structured `op:tuple` with each element evaluated.
           (if (null? tuple-arg*)
               (list (cons "op" "lit")
                     (cons "type" (list (cons "type" "Void")))
                     (cons "value" ""))
               (list (cons "op" "tuple")
                     (cons "elements"
                           (list->vector
                             (map (lambda (ta)
                                    (nanopass-case (Lnovectorref Tuple-Argument) ta
                                      [(single ,src ,expr) (emit-ir-expr expr)]
                                      [(spread ,src ,nat ,expr)
                                       (list (cons "op" "spread")
                                             (cons "length" nat)
                                             (cons "expr" (emit-ir-expr expr)))]))
                                  tuple-arg*)))))]
          [(vector ,src ,tuple-arg* ...)
           ;; Vector literal — Compact's `Vector<N, T>` is laid out as a
           ;; tuple at the IR level (the consumer indexes it via `index`).
           ;; Emit `op:tuple` with one element per source element. Each
           ;; source element is a `Tuple-Argument` node; we recurse through
           ;; its inner expression.
           (list (cons "op" "tuple")
                 (cons "elements"
                       (list->vector
                         (map (lambda (ta)
                                (nanopass-case (Lnovectorref Tuple-Argument) ta
                                  [(single ,src ,expr) (emit-ir-expr expr)]
                                  [(spread ,src ,nat ,expr)
                                   (list (cons "op" "spread")
                                         (cons "length" nat)
                                         (cons "expr" (emit-ir-expr expr)))]))
                              tuple-arg*))))]
          [(bytes->field ,src ,len ,expr)
           ;; Reinterpret a Bytes value as a Field element.
           (list (cons "op" "bytes-to-field")
                 (cons "length" len)
                 (cons "expr" (emit-ir-expr expr)))]
          [(field->bytes ,src ,len ,expr)
           ;; Reinterpret a Field element as a Bytes value.
           (list (cons "op" "field-to-bytes")
                 (cons "length" len)
                 (cons "expr" (emit-ir-expr expr)))]
          [(bytes->vector ,src ,len ,expr)
           ;; View a Bytes value as Vector<len, Uint<255>>.
           (list (cons "op" "bytes-to-vector")
                 (cons "length" len)
                 (cons "expr" (emit-ir-expr expr)))]
          [(vector->bytes ,src ,len ,expr)
           ;; View a Vector<len, Uint<255>> as Bytes.
           (list (cons "op" "vector-to-bytes")
                 (cons "length" len)
                 (cons "expr" (emit-ir-expr expr)))]
          [(contract-call ,src ,elt-name (,expr ,type) ,expr* ...)
           ;; Cross-contract circuit invocation: call `elt-name` on the
           ;; contract value `expr` (of type `type`) with arguments.
           (list (cons "op" "contract-call")
                 (cons "circuit" (symbol->string elt-name))
                 (cons "contract" (emit-ir-expr expr))
                 (cons "contract-type" (ir-type->json type))
                 (cons "args" (list->vector (map emit-ir-expr expr*))))]
          [else
           ;; Defensive: unrecognized Lnovectorref Expression form. With the
           ;; coverage contracts (election, bboard, micro-dao) this never
           ;; fires, but the fallback keeps the pass total in case the
           ;; grammar grows.
           (list (cons "op" "lit")
                 (cons "type" (list (cons "type" "Void")))
                 (cons "value" ""))]))

      ;; Deterministic ordering for hashtable-derived JSON arrays: sort the
      ;; emitted objects by their "name" field. eq-hashtable iteration order is
      ;; unspecified, which made contract-info.json non-reproducible across
      ;; compiles; sorting keeps it stable.
      (define (json-name obj)
        (let ([n (cond [(assoc "name" obj) => cdr] [else ""])])
          (if (symbol? n) (symbol->string n) n)))
      (define (sort-json-by-name objs)
        (sort (lambda (a b) (string<? (json-name a) (json-name b))) objs))

      ;; Emit a circuit body expression as a statement tree.
      (define (emit-ir-body the-expr)
        (nanopass-case (Lnovectorref Expression) the-expr
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
       ;; Populate signature-table (native/witness dispatch + result type) and
       ;; lowered-body-table (per-circuit body for the `ir` field) from the
       ;; lowered (Lnovectorref) program. Working off the lowered form means
       ;; enums, loops and helper calls are already resolved, and the body and
       ;; its types live in a single language.
       (nanopass-case (Lnovectorref Program) novectorref-ir
         [(program ,src ((,export-name* ,name*) ...) ,pelt* ...)
          (for-each
            (lambda (pelt)
              (nanopass-case (Lnovectorref Program-Element) pelt
                [(circuit ,src ,function-name (,arg* ...) ,type ,expr)
                 (hashtable-set! lowered-body-table (id-sym function-name) expr)]
                [(native ,src ,function-name ,native-entry (,arg* ...) ,type)
                 (let ([cls (native-entry-class native-entry)])
                   (hashtable-set! signature-table
                                   (id-sym function-name)
                                   (list (if (eq? cls 'witness) 'native-witness 'native-circuit)
                                         type)))]
                [(witness ,src ,function-name (,arg* ...) ,type)
                 (hashtable-set! signature-table
                                 (id-sym function-name)
                                 (list 'witness-decl type))]
                [else (void)]))
            pelt*)])
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
               "structs"
               (list->vector
                 (let ([acc '()])
                   (let-values ([(keys vals) (hashtable-entries struct-table)])
                     (vector-for-each
                       (lambda (k v)
                         ;; `v` is `(unique-name fields-vector-or-#f)`. Skip
                         ;; entries whose fields slot is still the placeholder.
                         (when (and (pair? v) (vector? (cadr v)))
                           (set! acc
                                 (cons (list (cons "name" (car v))
                                             (cons "fields" (cadr v)))
                                       acc))))
                       keys vals))
                   (sort-json-by-name acc))))
            )))
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
                     ;; The body is taken from the lowered (Lnovectorref)
                     ;; program, looked up by circuit name.
                     (let ([lowered-body (hashtable-ref lowered-body-table
                                                        (id-sym function-name) #f)])
                       (if lowered-body
                           (list
                             (cons "body" (emit-ir-body lowered-body))
                             (cons "result" (void)))
                           (void)))
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
