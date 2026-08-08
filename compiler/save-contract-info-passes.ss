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

  ;; The version of this format, which is the compatibility contract for a
  ;; consumer. It is independent of the compiler, language and runtime
  ;; versions beside it in the file: a compiler release that does not change
  ;; the schema leaves it alone, and a schema change can ship without a
  ;; language change. Bump the major for a removal, a repurposed field or a
  ;; changed meaning; bump the minor for an additive, backward-compatible one.
  (define contract-info-version-string "0.1.0")

  ;; Render an identifier for the portable IR.
  ;;
  ;; Inlining renames locals with `make-temp-id`, which keeps the original
  ;; symbol, so a circuit that inlines several helpers ends up with many
  ;; distinct bindings all named `tmp`. The internal form distinguishes them
  ;; by id identity, but emitting the bare symbol collapses them: a consumer
  ;; sees `[let tmp = a, let tmp = b]` with two `var tmp` references and
  ;; cannot tell which binding each reference means. Qualifying temps with
  ;; their unique id keeps binding and reference sites in agreement.
  ;; Source-level names are already distinct within their scope and are
  ;; emitted as written, so circuit arguments stay addressable by name.
  (define (ir-var-name var-name)
    (if (id-temp? var-name)
        (format "~a.~a" (id-sym var-name) (id-uniq var-name))
        (symbol->string (id-sym var-name))))

  ; NB: must come after identify-pure-circuits
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

      ;; An integer literal ADT-op argument carrying its declared type.
      ;;
      ;; A bare `(quote <n>)` argument would be emitted as a generic Field
      ;; literal, while the TypeScript codegen at the same site encodes it
      ;; through the ledger operation's declared argument type (an enum cell
      ;; write is a 1-byte value, not a field element). Wrapping the literal
      ;; keeps the on-chain encoding width in the IR.
      (define-record-type typed-lit
        (nongenerative)
        (fields value type-json))

      ;; VM alignment entries carry a Uint type.
      (define (vm-uint-type-json maxval)
        (list (cons "type-name" "Uint") (cons "maxval" maxval)))

      ;; Convert a VMop value to JSON-safe form.
      (define (vmop->json v)
        (cond
          [(typed-lit? v)
           (list (cons "op" "lit")
                 (cons "type" (typed-lit-type-json v))
                 (cons "value" (number->string (typed-lit-value v))))]
          [(integer? v) v]
          [(boolean? v) v]
          [(string? v) v]
          [(emitted-json? v) v]
          [(list? v) (list->vector (map vmop->json v))]
          [(VMop? v)
           (VMop-case v
             [(VMstack) "stack"]
             [(VMvoid) (void)]
             [(VMsuppress) (void)]
             [(VMalign value bytes)
              (list (cons "tag" "value")
                    (cons "value" (number->string value))
                    (cons "type" (vm-uint-type-json (- (expt 2 (* bytes 8)) 1))))]
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
             ;; The remaining state values carry structure, so unlike a cell
             ;; they cannot be represented by their contents alone. They are
             ;; keyed on `state`, which no expression or path element uses.
             [(VMstate-value-array val*)
              (list (cons "state" "array")
                    (cons "values" (list->vector (map vmop->json val*))))]
             [(VMstate-value-map key* val*)
              (list (cons "state" "map")
                    (cons "entries" (list->vector (map state-entry->json key* val*))))]
             [(VMstate-value-merkle-tree nat key* val*)
              (list (cons "state" "merkle-tree")
                    (cons "depth" (vmop->json nat))
                    (cons "entries" (list->vector (map state-entry->json key* val*))))]
             ;; Values the consumer computes at run time, keyed on `vm`.
             [(VM+ x y)
              (list (cons "vm" "add")
                    (cons "left" (vmop->json x))
                    (cons "right" (vmop->json y)))]
             [(VMaligned-concat x*)
              (list (cons "vm" "aligned-concat")
                    (cons "values" (list->vector (map vmop->json x*))))]
             [(VMnull x)
              (list (cons "vm" "null") (cons "value" (vmop->json x)))]
             [(VMmax-sizeof x)
              (list (cons "vm" "max-sizeof") (cons "value" (vmop->json x)))]
             [(VMleaf-hash x)
              (list (cons "vm" "leaf-hash") (cons "value" (vmop->json x)))]
             [(VMcoin-commit coin recipient)
              (list (cons "vm" "coin-commit")
                    (cons "coin" (vmop->json coin))
                    (cons "recipient" (vmop->json recipient)))]
             [else
              (internal-errorf #f "no JSON encoding for VM value: ~s" v)])]
          [else
           (guard (c [#t (format "~s" v)])
             (nd-emit-ir-expr v))]))

      (define (state-entry->json k v)
        (list (cons "key" (vmop->json k)) (cons "value" (vmop->json v))))

      ;; Render one `idx` path element. An element is a constant (a VMalign,
      ;; already tagged), the VM stack, or a runtime expression: a nested ADT
      ;; access such as `m.lookup(k).insert(...)` indexes by the value of `k`.
      ;; Each kind carries its own tag, because an untagged expression would
      ;; otherwise reach the value branch and be coerced to its printed
      ;; representation, which the consumer cannot evaluate.
      ;; A dynamic path element arrives already serialized, because the caller
      ;; emits the index expression before handing it to the VM expander. It
      ;; must not go through `vmop->json`, which would read the JSON alist as
      ;; a plain list and rewrite it as an array of printed pairs.
      (define (emitted-json? p)
        (and (pair? p) (pair? (car p)) (string? (caar p))))

      (define (path-elt->json p)
        ;; An element reaches this either already serialized (a sugar path
        ;; element, emitted before the VM expander ran) or as a raw node that
        ;; `vmop->json` serializes here. A ledger-op argument takes the second
        ;; route, which is how `m.lookup(k)` indexes by the value of `k`.
        (let ([v (if (emitted-json? p) p (vmop->json p))])
          (cond
            [(and (list? v) (assoc "tag" v)) v]
            [(equal? v "stack") (list (cons "tag" "stack"))]
            [(and (list? v) (assoc "op" v))
             (if (equal? (cdr (assoc "op" v)) "var")
                 (list (cons "tag" "var") (cons "name" (cdr (assoc "name" v))))
                 (list (cons "tag" "expr") (cons "expr" v)))]
            [else
             (list (cons "tag" "value")
                   (cons "value" (format "~a" v))
                   (cons "type" (vm-uint-type-json 255)))])))

      ;; `suppress-null` and `suppress-zero` (vm.ss) replace an operand with
      ;; VMsuppress when the instruction would do nothing: an `idx` with an
      ;; empty path, an `ins` of zero elements. The instruction is then not
      ;; part of the program.
      (define (vm-suppressed? v)
        (and (VMop? v) (VMop-case v [(VMsuppress) #t] [else #f])))

      ;; Convert a vminstr to IR LedgerOp JSON, or #f when the instruction is
      ;; suppressed and carries nothing to emit. Every other failure is an
      ;; error: the callers drop only #f, so a malformed op is loud.
      (define (vminstr->ir-json vi)
        (let ([op (vminstr-op vi)] [args (vminstr-arg* vi)])
          (define (get-arg name) (cdr (assoc name args)))
          (define (has-arg? name) (assoc name args))
          (cond
            [(ormap (lambda (a) (vm-suppressed? (cdr a))) args) #f]
            [(string=? op "idx")
             (let ([cached (get-arg "cached")]
                   [push-path (get-arg "pushPath")]
                   [path (get-arg "path")])
               (list (cons "op" "idx")
                     (cons "cached" (if cached #t #f))
                     (cons "push-path" (if push-path #t #f))
                     (cons "path" (list->vector (map path-elt->json path)))))]
            [(string=? op "addi")
             (list (cons "op" "addi")
                   (cons "immediate" (vmop->json (get-arg "immediate"))))]
            [(string=? op "ins")
             (let ([n-val (vmop->json (get-arg "n"))])
               ;; A suppressed `ins` carries no count and is not an instruction.
               (if (or (eq? n-val (void)) (not (integer? n-val)))
                   #f
                   (list (cons "op" "ins")
                         (cons "cached" (if (get-arg "cached") #t #f))
                         (cons "n" n-val))))]
            [(string=? op "dup")
             ;; Emit the stack arity `n`. `dup{n}` duplicates the stack element
             ;; `n` below the top; without it the IR consumer can only assume
             ;; `n=0` (dup the top), which mis-navigates the VM stack for
             ;; context reads (`kernel.self()` is `dup{n:2}`) and the
             ;; mint/spend kernel effects (`dup{n:1}`/`dup{n:2}`).
             (list (cons "op" "dup")
                   (cons "n" (if (has-arg? "n") (vmop->json (get-arg "n")) 0)))]
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
             ;; midnight-ledger.ss emits `rem` with a cached flag only.
             (list (cons "op" "rem")
                   (cons "cached" (if (and (has-arg? "cached") (get-arg "cached")) #t #f)))]
            [(string=? op "noop")
             (list (cons "op" "noop")
                   (cons "n" (if (has-arg? "n") (vmop->json (get-arg "n")) 0)))]
            [else
             (cons (cons "op" op)
                   (map (lambda (a) (cons (car a) (vmop->json (cdr a)))) args))])))


      ;; Deterministic ordering for hashtable-derived JSON arrays: sort the
      ;; emitted objects by their "name" field. eq-hashtable iteration order is
      ;; unspecified, which made contract-info.json non-reproducible across
      ;; compiles; sorting keeps it stable.
      (define (json-name obj)
        (let ([n (cond [(assoc "name" obj) => cdr] [else ""])])
          (if (symbol? n) (symbol->string n) n)))
      (define (sort-json-by-name objs)
        (sort (lambda (a b) (string<? (json-name a) (json-name b))) objs))

      ;; ---------------------------------------------------------------
      ;; Body emitter. Bodies serialize from the analyzed program itself:
      ;; enum members and helper circuits stay by name, loops stay loops,
      ;; and body types use the same `type-name` encoding as the signatures
      ;; (the `Type` transformer). Ledger operations expand to Impact VM ops.
      ;; ---------------------------------------------------------------

      ;; function id -> (arg* result-type body-expr), every circuit
      ;; definition in the analyzed program. Keyed on the id record, not on
      ;; its symbol: a generic circuit is monomorphized into one definition
      ;; per instantiation, and those share a symbol while carrying different
      ;; argument and result types.
      (define nd-circuit-table (make-eq-hashtable))

      ;; function id -> the name that identifies it in `helpers` and at every
      ;; call site. Instantiations of one generic are numbered apart, as the
      ;; TypeScript backend numbers its own bindings.
      (define nd-name-table (make-eq-hashtable))
      (define nd-name-counts (make-eq-hashtable))

      (define (nd-circuit-name fn-id)
        (or (hashtable-ref nd-name-table fn-id #f)
            (let* ([sym (id-sym fn-id)]
                   [n (hashtable-ref nd-name-counts sym 0)]
                   [name (if (eqv? n 0)
                             (symbol->string sym)
                             (format "~a_~a" sym n))])
              (hashtable-set! nd-name-counts sym (+ n 1))
              (hashtable-set! nd-name-table fn-id name)
              name)))

      ;; function-name-symbol -> (class result-type) for native and
      ;; witness declarations in the analyzed program.
      (define nd-signature-table (make-eq-hashtable))

      ;; Circuit names referenced by emitted call nodes; drives the
      ;; top-level `helpers` array (the consumer's call table).
      (define nd-called (make-eq-hashtable))

      (define (nd-lit type-json value-str)
        (list (cons "op" "lit") (cons "type" type-json) (cons "value" value-str)))

      (define (nd-quote-lit datum)
        (cond
          [(boolean? datum)
           (nd-lit (list (cons "type-name" "Boolean")) (if datum "true" "false"))]
          [(and (integer? datum) (exact? datum))
           (nd-lit (list (cons "type-name" "Field")) (number->string datum))]
          [(bytevector? datum)
           (nd-lit (list (cons "type-name" "Bytes")
                         (cons "length" (bytevector-length datum)))
                   (apply string-append
                          (map (lambda (b)
                                 (let ([s (number->string b 16)])
                                   (if (< b 16) (string-append "0" s) s)))
                               (bytevector->u8-list datum))))]
          [else (error 'nd-quote-lit "unsupported literal datum")]))

      ;; Wrap an integer-literal ADT-op argument with its declared type,
      ;; as typed-op-arg does for the lowered emitter.
      (define (nd-typed-op-arg type expr)
        (nanopass-case (Lnodisclose Expression) expr
          [(quote ,src ,datum)
           (if (and (integer? datum) (exact? datum))
               (make-typed-lit datum (Type type))
               expr)]
          [else expr]))

      (define (nd-binop op e1 e2)
        (list (cons "op" op)
              (cons "left" (nd-emit-ir-expr e1))
              (cons "right" (nd-emit-ir-expr e2))))

      (define (nd-cast from-json to-json e)
        (list (cons "op" "cast")
              (cons "expr" (nd-emit-ir-expr e))
              (cons "from" from-json)
              (cons "to" to-json)))

      (define (nd-tuple-arg ta)
        (nanopass-case (Lnodisclose Tuple-Argument) ta
          [(single ,src ,expr) (nd-emit-ir-expr expr)]
          [(spread ,src ,nat ,expr)
           (list (cons "op" "spread")
                 (cons "length" nat)
                 (cons "expr" (nd-emit-ir-expr expr)))]))

      (define (nd-map-arg ma)
        (nanopass-case (Lnodisclose Map-Argument) ma
          [(,expr ,type ,type^) (nd-emit-ir-expr expr)]))

      ;; A map/fold callee: an inline lambda emits as {params, body}; a
      ;; named function emits as {call} and joins the helpers worklist.
      (define (nd-fun->json fun)
        (nanopass-case (Lnodisclose Function) fun
          [(fref ,src ,function-name)
           (if (hashtable-contains? nd-circuit-table function-name)
               (begin
                 (hashtable-set! nd-called function-name #t)
                 (list (cons "call" (nd-circuit-name function-name))))
               (list (cons "call" (symbol->string (id-sym function-name)))))]
          [(circuit ,src (,arg* ...) ,type ,expr)
           (list (cons "params"
                       (list->vector
                         (map (lambda (a)
                                (nanopass-case (Lnodisclose Argument) a
                                  [(,var-name ,type)
                                   (list (cons "name" (ir-var-name var-name))
                                         (cons "type" (Type type)))]))
                              arg*)))
                 (cons "body" (nd-emit-ir-expr expr)))]))

      (define (nd-emit-ir-expr expr)
        (nanopass-case (Lnodisclose Expression) expr
          [(var-ref ,src ,var-name)
           (list (cons "op" "var") (cons "name" (ir-var-name var-name)))]
          [(quote ,src ,datum) (nd-quote-lit datum)]
          [(assert ,src ,expr ,mesg)
           (list (cons "op" "assert")
                 (cons "expr" (nd-emit-ir-expr expr))
                 (cons "message" mesg))]
          [(if ,src ,expr0 ,expr1 ,expr2)
           (list (cons "op" "if-expr")
                 (cons "cond" (nd-emit-ir-expr expr0))
                 (cons "then" (nd-emit-ir-expr expr1))
                 (cons "else" (nd-emit-ir-expr expr2)))]
          [(+ ,src ,mbits ,expr1 ,expr2) (nd-binop "add" expr1 expr2)]
          [(- ,src ,mbits ,expr1 ,expr2) (nd-binop "sub" expr1 expr2)]
          [(* ,src ,mbits ,expr1 ,expr2) (nd-binop "mul" expr1 expr2)]
          [(== ,src ,type ,expr1 ,expr2) (nd-binop "eq" expr1 expr2)]
          [(!= ,src ,type ,expr1 ,expr2) (nd-binop "neq" expr1 expr2)]
          [(< ,src ,bits ,expr1 ,expr2) (nd-binop "lt" expr1 expr2)]
          [(<= ,src ,bits ,expr1 ,expr2) (nd-binop "le" expr1 expr2)]
          [(> ,src ,bits ,expr1 ,expr2) (nd-binop "gt" expr1 expr2)]
          [(>= ,src ,bits ,expr1 ,expr2) (nd-binop "ge" expr1 expr2)]
          [(elt-ref ,src ,expr ,elt-name ,nat)
           (list (cons "op" "field")
                 (cons "expr" (nd-emit-ir-expr expr))
                 (cons "name" (symbol->string elt-name)))]
          [(tuple-ref ,src ,expr ,kindex)
           (list (cons "op" "index")
                 (cons "expr" (nd-emit-ir-expr expr))
                 (cons "index" kindex))]
          [(vector-ref ,src ,type ,expr ,index)
           (list (cons "op" "vector-index")
                 (cons "expr" (nd-emit-ir-expr expr))
                 (cons "index" (nd-emit-ir-expr index)))]
          [(enum-ref ,src ,type ,elt-name)
           (list (cons "op" "enum-member")
                 (cons "type" (Type type))
                 (cons "member" (symbol->string elt-name)))]
          [(cast-from-enum ,src ,type ,type^ ,expr)
           (nd-cast (Type type^) (Type type) expr)]
          [(cast-to-enum ,src ,type ,type^ ,expr)
           (nd-cast (Type type^) (Type type) expr)]
          [(cast-from-bytes ,src ,type ,len ,expr)
           (nd-cast (list (cons "type-name" "Bytes") (cons "length" len))
                    (Type type)
                    expr)]
          [(safe-cast ,src ,type ,type^ ,expr)
           (nd-cast (Type type^) (Type type) expr)]
          [(downcast-unsigned ,src ,nat? ,nat ,expr)
           ;; The operand width is optional; without it the source is a Field.
           (nd-cast (if nat?
                        (list (cons "type-name" "Uint") (cons "maxval" nat?))
                        (list (cons "type-name" "Field")))
                    (list (cons "type-name" "Uint") (cons "maxval" nat))
                    expr)]
          [(call ,src ,function-name ,expr* ...)
           (let* ([fn-sym (id-sym function-name)]
                  [name (symbol->string fn-sym)]
                  [json-args (list->vector (map nd-emit-ir-expr expr*))])
             (cond
               [(hashtable-contains? nd-circuit-table function-name)
                (hashtable-set! nd-called function-name #t)
                (let ([result-type (cadr (hashtable-ref nd-circuit-table function-name #f))])
                  (list (cons "op" "call-pure")
                        (cons "name" (nd-circuit-name function-name))
                        (cons "args" json-args)
                        (cons "result-type" (Type result-type))))]
               [(hashtable-contains? nd-signature-table fn-sym)
                (let* ([sig (hashtable-ref nd-signature-table fn-sym #f)]
                       [op (if (eq? (car sig) 'native-circuit) "call-pure" "call-witness")])
                  (list (cons "op" op)
                        (cons "name" name)
                        (cons "args" json-args)
                        (cons "result-type" (Type (cadr sig)))))]
               [else (error 'nd-emit-ir-expr "unknown callee" fn-sym)]))]
          [(map ,src ,len ,fun ,map-arg ,map-arg* ...)
           (list (cons "op" "map")
                 (cons "length" len)
                 (cons "fun" (nd-fun->json fun))
                 (cons "args" (list->vector (map nd-map-arg (cons map-arg map-arg*)))))]
          [(fold ,src ,len ,fun (,expr0 ,type0) ,map-arg ,map-arg* ...)
           (list (cons "op" "fold")
                 (cons "length" len)
                 (cons "fun" (nd-fun->json fun))
                 (cons "init" (nd-emit-ir-expr expr0))
                 (cons "args" (list->vector (map nd-map-arg (cons map-arg map-arg*)))))]
          [(let* ,src ([,local* ,expr*] ...) ,expr)
           (let ([let-stmts (map (lambda (loc bind-expr)
                                   (list (cons "op" "let")
                                         (cons "name"
                                               (nanopass-case (Lnodisclose Argument) loc
                                                 [(,var-name ,type) (ir-var-name var-name)]))
                                         (cons "value" (nd-emit-ir-expr bind-expr))))
                                 local* expr*)]
                 [body-expr (nd-emit-ir-expr expr)])
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
                                         [(,src ,type ,expr) (nd-emit-ir-expr expr)]))
                                     path-elt*)]
                     [arg-alist (append
                                  (map (lambda (f a) (cons f a)) adt-formal* adt-arg*)
                                  (map (lambda (vn ty ex) (cons (id-sym vn) (nd-typed-op-arg ty ex)))
                                       var-name* type* expr*))]
                     [result-type (Type type)]
                     [vminstr* (expand-vm-code src path-vals #f arg-alist (vm-code-code vm-code))]
                     [json-ops (fold-right
                                 (lambda (vi acc)
                                   (let ([json (vminstr->ir-json vi)])
                                     (if json (cons json acc) acc)))
                                 '()
                                 vminstr*)])
                (list (cons "op" "ledger-query")
                      (cons "ops" (list->vector json-ops))
                      (cons "result-type" result-type)))])]
          [(default ,src ,type)
           (list (cons "op" "default") (cons "type" (Type type)))]
          [(new ,src ,type ,expr* ...)
           (list (cons "op" "new")
                 (cons "type" (Type type))
                 (cons "elements" (list->vector (map nd-emit-ir-expr expr*))))]
          [(seq ,src ,expr* ... ,expr)
           (let loop ([rest expr*] [n 0])
             (if (null? rest)
                 (nd-emit-ir-expr expr)
                 (list (cons "op" "let-expr")
                       (cons "bindings"
                             (list->vector
                               (list (list (cons "op" "let")
                                           (cons "name" (format "__seq_~a" n))
                                           (cons "value" (nd-emit-ir-expr (car rest)))))))
                       (cons "body" (loop (cdr rest) (+ n 1))))))]
          [(return ,src ,expr) (nd-emit-ir-expr expr)]
          [(tuple ,src ,tuple-arg* ...)
           (list (cons "op" "tuple")
                 (cons "elements" (list->vector (map nd-tuple-arg tuple-arg*))))]
          [(vector ,src ,tuple-arg* ...)
           (list (cons "op" "tuple")
                 (cons "elements" (list->vector (map nd-tuple-arg tuple-arg*))))]
          [(field->bytes ,src ,len ,expr)
           (list (cons "op" "field-to-bytes")
                 (cons "length" len)
                 (cons "expr" (nd-emit-ir-expr expr)))]
          [(bytes->vector ,src ,len ,expr)
           (list (cons "op" "bytes-to-vector")
                 (cons "length" len)
                 (cons "expr" (nd-emit-ir-expr expr)))]
          [(vector->bytes ,src ,len ,expr)
           (list (cons "op" "vector-to-bytes")
                 (cons "length" len)
                 (cons "expr" (nd-emit-ir-expr expr)))]
          [(contract-call ,src ,elt-name (,expr ,type) ,expr* ...)
           (list (cons "op" "contract-call")
                 (cons "circuit" (symbol->string elt-name))
                 (cons "contract" (nd-emit-ir-expr expr))
                 (cons "contract-type" (Type type))
                 (cons "args" (list->vector (map nd-emit-ir-expr expr*))))]
          [(bytes-ref ,src ,type ,expr ,index)
           ;; One byte of a Bytes value; the index is a runtime expression.
           (list (cons "op" "bytes-index")
                 (cons "expr" (nd-emit-ir-expr expr))
                 (cons "index" (nd-emit-ir-expr index)))]
          [(tuple-slice ,src ,type ,expr ,kindex ,len)
           ;; Constant-index slice of a tuple or vector. The operand type
           ;; rides along: slicing a heterogeneous tuple yields element types
           ;; the consumer cannot recover from the length alone.
           (list (cons "op" "tuple-slice")
                 (cons "expr" (nd-emit-ir-expr expr))
                 (cons "index" kindex)
                 (cons "length" len)
                 (cons "type" (Type type)))]
          [(vector-slice ,src ,type ,expr ,index ,len)
           (list (cons "op" "vector-slice")
                 (cons "expr" (nd-emit-ir-expr expr))
                 (cons "index" (nd-emit-ir-expr index))
                 (cons "length" len)
                 (cons "type" (Type type)))]
          [(bytes-slice ,src ,type ,expr ,index ,len)
           ;; The result is always Bytes of `length`, so it needs no type.
           (list (cons "op" "bytes-slice")
                 (cons "expr" (nd-emit-ir-expr expr))
                 (cons "index" (nd-emit-ir-expr index))
                 (cons "length" len))]
          [else
           ;; Every Lnodisclose expression form must have a clause above.
           ;; Name the offender instead of letting nanopass abort with its
           ;; own empty-else message, which does not say what it hit.
           (internal-errorf #f
                            "no analyzed-IR emitter clause for expression: ~s"
                            (unparse-Lnodisclose expr))]))

      (define (nd-emit-ir-body the-expr)
        (nanopass-case (Lnodisclose Expression) the-expr
          [(seq ,src ,expr* ... ,expr)
           (list (cons "op" "seq")
                 (cons "stmts"
                       (list->vector
                         (map (lambda (e)
                                (list (cons "op" "expr-stmt")
                                      (cons "expr" (nd-emit-ir-expr e))))
                              (append expr* (list expr))))))]
          [else
           (list (cons "op" "seq")
                 (cons "stmts" (list->vector
                                 (list (list (cons "op" "expr-stmt")
                                             (cons "expr" (nd-emit-ir-expr the-expr)))))))]))

      ;; One entry per called circuit: the consumer's call table. `body`
      ;; stays an empty statement list and `result` carries the circuit's
      ;; body expression (a Compact circuit returns its final expression).
      (define (nd-emit-helper-def fn-id entry)
        (list
          (cons "name" (nd-circuit-name fn-id))
          (cons "params"
                (list->vector
                  (map (lambda (a)
                         (nanopass-case (Lnodisclose Argument) a
                           [(,var-name ,type)
                            (list (cons "name" (ir-var-name var-name))
                                  (cons "type" (Type type)))]))
                       (car entry))))
          (cons "body" (list (cons "op" "seq") (cons "stmts" (list->vector '()))))
          (cons "result" (nd-emit-ir-expr (caddr entry)))))

      ;; Emitting a helper body can reference more circuits, so drain to
      ;; a fixpoint before assembling the array.
      (define (nd-emit-helpers)
        (let ([done (make-eq-hashtable)])
          (let loop ([acc '()])
            (let* ([keys (vector->list (hashtable-keys nd-called))]
                   [pending (filter (lambda (k)
                                      (and (hashtable-contains? nd-circuit-table k)
                                           (not (hashtable-contains? done k))))
                                    keys)])
              (if (null? pending)
                  (sort-json-by-name acc)
                  (loop (append
                          (map (lambda (k)
                                 (hashtable-set! done k #t)
                                 (nd-emit-helper-def k (hashtable-ref nd-circuit-table k #f)))
                               pending)
                          acc))))))))

    (Program : Program (ir) -> Program ()
      [(program ,src (,contract-name* ...) ((,export-name* ,name*) ...) ,pelt* ...)
       ;; Index the program's own definitions so body emission can dispatch
       ;; calls and build the helpers array.
       (for-each
           (lambda (pelt)
             (nanopass-case (Lnodisclose Program-Element) pelt
               [(circuit ,src ,function-name (,arg* ...) ,type ,expr)
                ;; Claim the name in declaration order, so output is stable.
                (nd-circuit-name function-name)
                (hashtable-set! nd-circuit-table
                                function-name
                                (list arg* type expr))]
               [(native ,src ,function-name ,native-entry (,arg* ...) ,type)
                (let ([cls (native-entry-class native-entry)])
                  (hashtable-set! nd-signature-table
                                  (id-sym function-name)
                                  (list (if (eq? cls 'witness) 'native-witness 'native-circuit)
                                        type)))]
               [(witness ,src ,function-name (,arg* ...) ,type)
                (hashtable-set! nd-signature-table
                                (id-sym function-name)
                                (list 'witness-decl type))]
             [else (void)]))
         pelt*)
       (let* ([op (get-target-port 'contract-info.json)]
              ;; The circuits entry must be built before the helpers entry:
              ;; emitting circuit bodies populates the called-circuits set
              ;; the helpers array drains.
              [head
               (list
                 (cons
                   "contract-info-version"
                   contract-info-version-string)
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
                   "constructor"
                   (fold-right LedgerConstructor (void) pelt*)))]
              [tail
               (list (cons "helpers" (list->vector (nd-emit-helpers))))])
         (print-json op (append head tail)))
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
             "result-type"
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
    ;; The constructor computes the contract initial ledger state, so a
    ;; consumer needs its body to deploy. Its arguments are the deploy-time
    ;; parameters.
    (LedgerConstructor : Program-Element (ir acc) -> * (json)
      (definitions
        ;; The unit value, which is the whole body of a constructor the source
        ;; did not write.
        (define (unit? e)
          (nanopass-case (Lnodisclose Expression) e
            [(tuple ,src ,tuple-arg* ...) (null? tuple-arg*)]
            [(seq ,src ,expr* ... ,expr) (and (null? expr*) (unit? expr))]
            [else #f]))
        ;; A constructor that takes nothing and does nothing carries nothing:
        ;; a field the constructor never writes takes its default from the
        ;; ledger layout either way, so an empty body would say only what its
        ;; absence already says.
        (define (says-nothing? arg* expr)
          (and (null? arg*) (unit? expr))))
      [(public-ledger-declaration ,pl-array ,lconstructor)
       (nanopass-case (Lnodisclose Ledger-Constructor) lconstructor
         [(constructor ,src (,arg* ...) ,expr)
          (if (says-nothing? arg* expr)
              (void)
              (list (cons "arguments" (list->vector (map Argument arg*)))
                    (cons "body" (nd-emit-ir-body expr))))])]
      [else acc])

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
                 (list
                   (cons "body" (nd-emit-ir-body expr))
                   (cons "result" (void)))))
             circuit*))
         circuit*
         (external-names function-name))]
      [else circuit*])
    (Argument : Argument (ir) -> * (json)
      [(,var-name ,type)
       (list
         (cons
           "name"
           (ir-var-name var-name))
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
         ;; A maxval reaches 2^254-1. It stays a JSON number, which is what
         ;; the compiler's own reader for an imported contract requires; a
         ;; consumer must parse it with arbitrary precision.
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
      [(tunknown)
       ;; The element type of an empty vector, reached through the loop
       ;; parameter of a zero-trip `for`. No value of this type is ever
       ;; materialized, so it maps to the unit type and the vocabulary
       ;; the consumer must match stays closed.
       (list
         (cons "type-name" "Tuple")
         (cons "types" (list->vector '())))]
      [else (assert cannot-happen)]))

  (define-passes save-contract-info-passes
    (save-contract-info              Lnodisclose))
)
