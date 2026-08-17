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

(define (save-analyzed-ir ir proof-circuit-name*)
  (let ([sexp (extract-analyzed-ir ir proof-circuit-name*)])
    (cond
      ;; The hook takes the datum and the directory as arguments, so it needs
      ;; no import from the compiler and runs in a binary built without
      ;; visible libraries.
      [(analyzed-ir-hook) => (lambda (hook) (hook sexp (target-directory)))]
      [else
       (let ([op (get-target-port 'analyzed-ir.sexp)])
         ;; Parentheses only: brackets are a Chez pretty-printing style, and a
         ;; non-Scheme reader should not need to treat them as paren synonyms.
         (parameterize ([print-brackets #f])
           (pretty-print sexp op)))]))
  ir)
