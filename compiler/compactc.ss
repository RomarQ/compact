#! /usr/bin/env -S scheme --compile-imported-libraries --program
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

(import (except (chezscheme) errorf)
        (command-line-parsing)
        (config-params)
        (program-common)
        (passes)
        (utils))

(define (print-help)
  (print-usage #f)
  (fprintf (current-output-port) "
This program compiles the Compact source program in the file specified by
<source-pathname> and puts the resulting target files into the directory
specified by <target-directory-pathname>.  These target files include a
Typescript equivalent of the Compact source file, Zkir circuit equivalents of
the exported circuits, and proving keys created by running zkir on the zkir
circuits.

The following flags, if present, affect the compiler's behavior as follows:
  --help prints help text and exits.

  --version prints the compiler version and exits.

  --language-version prints the language version and exits.

  --ledger-version prints the ledger version and exits.  The ledger version
    is the version of the ledger that is expected by the generated code.

  --runtime-version prints the runtime version and exits.  The runtime version
    is the version of the Compact runtime JavaScript package that is used by
    generated contract code.

  --feature-zkir-v3 causes the compiler to generate circuits using ZKIR version 3,
    overriding the default (version 2).

  --vscode causes error messages to be printed on a single line so they are
    rendered properly within the VS Code extension for Compact.

  --skip-zk causes the compiler to skip the generation of proving keys.
    Generating proving keys can be time-consuming, so this option is useful when
    debugging only the Typescript output.  The compiler also skips, after
    printing a warning message, the generation of proving keys when it cannot
    find zkir.

  --no-communications-commitment omits the contract communications commitment
    that enables data integrity for contract-to-contract calls.

  --sourceRoot <sourceRoot value> overrides the compiler's setting of the
    sourceRoot field in the generated source-map (.js.map) file.  By default,
    the compiler tries to determine a useful value based on the source and
    target-directory pathnames, but this value might not be appropriate for the
    deployed structure of the application.

  --compact-path <search list> sets the compact path, overriding the default
    value, which is the value of the environment variable COMPACT_PATH, if
    it is set, and empty otherwise.  <search list> should be a colon-separated
    (semicolon-separated under Windows) sequence of directory pathnames.
    The compact path controls where the compiler looks for include and external
    module files with non-absolute pathnames.  It always looks first relative
    to the directory of the including or importing file, then in each directory
    in the compact path from left to right.

  --trace-search causes the compiler to print a sequence of messages saying
    where it is looking for each included file and imported module source file.

  --trace-passes causes the compiler to print tracing information that is
    generally useful only to compiler developers.

  --analyzed-ir causes the compiler to also write compiler/analyzed-ir.sexp
    into the target directory: the analyzed program printed in the compiler's
    own intermediate-language vocabulary, with each ledger operation and emit
    expanded to its Impact VM instructions, and with the export table and the
    exported/pure/proof flags made explicit.  An SDK in any language can
    execute circuits from this file with an interpreter.  The file is one
    S-expression datum.  The format follows the intermediate language, so it
    can change between compiler versions.

  --analyzed-ir-hook <pathname> loads the Scheme file at <pathname> and calls
    the procedure it defines under the name `hook` with the same datum
    --analyzed-ir writes, and with the target directory as a string.  The
    compiler writes no analyzed-ir.sexp in this mode.  The hook runs after
    the compile succeeds, and it decides what to do with the datum, so a consumer can render it in the encoding its
    own tools want.  The datum is ordinary data, so the file needs no import
    from the compiler.
"))

;; The loaded file sees only the bindings the boot file already provides, so a
;; hook that takes the datum needs no library from the compiler and the binary
;; keeps its libraries pruned.
(define (load-hook pathname)
  (define (complain)
    (external-errorf "the file loaded by --analyzed-ir-hook must define a procedure named hook"))
  (check-pathname pathname)
  (unless (file-exists? pathname)
    (external-errorf "the file named by --analyzed-ir-hook does not exist: ~a" pathname))
  (load pathname)
  (unless (top-level-bound? 'hook (interaction-environment)) (complain))
  (let ([hook (eval 'hook (interaction-environment))])
    (unless (procedure? hook) (complain))
    hook))

(usage "<flag> ... <source-pathname> <target-directory-pathname>")

(parameterize ([reset-handler abort])
  (command-line-case (command-line)
    [((flags [(--help) $ (begin (print-help) (exit))]
             [(--version) $ (begin (print-compiler-version) (exit))]
             [(--language-version) $ (begin (print-language-version) (exit))]
             [(--ledger-version) $ (begin (print-ledger-version ?--feature-zkir-v3) (exit))]
             [(--runtime-version) $ (begin (print-runtime-version) (exit))]
             [(--vscode)]
             [(--skip-zk)]
             [(--no-communications-commitment)]
             [(--sourceRoot) (string source-root)]
             [(--compact-path) (string search-list)]
             [(--trace-search)]
             [(--trace-passes)]
             [(--analyzed-ir)]
             [(--analyzed-ir-hook) (string analyzed-ir-hook-pathname)]
             [(--feature-zkir-v3)])
      (string source-pathname)
      (string target-directory-pathname))
     (check-pathname source-pathname)
     (check-pathname target-directory-pathname)
     (parameterize ([trace-passes ?--trace-passes]
                    [skip-zk ?--skip-zk]
                    [no-communications-commitment ?--no-communications-commitment]
                    [feature-zkir-v3 ?--feature-zkir-v3]
                    [write-analyzed-ir ?--analyzed-ir]
                    [compact-path (if ?--compact-path (split-search-path search-list) (compact-path))]
                    [trace-search ?--trace-search])
       (when source-root (register-source-root! source-root))
       (handle-exceptions ?--vscode
         ;; Load inside the handler: a missing or malformed hook file is
         ;; user input, and its error belongs in the same format as the rest.
         (parameterize ([analyzed-ir-hook
                          (and ?--analyzed-ir-hook
                               (load-hook analyzed-ir-hook-pathname))])
           (generate-everything source-pathname target-directory-pathname))))]
    [((flags [(--help) $ (begin (print-help) (exit))]
             [(--version) $ (begin (print-compiler-version) (exit))]
             [(--language-version) $ (begin (print-language-version) (exit))]
             [(--ledger-version) $ (begin (print-ledger-version ?--feature-zkir-v3) (exit))]
             [(--runtime-version) $ (begin (print-runtime-version) (exit))]
             [(--feature-zkir-v3)])
      (string arg) ...)
     (print-usage #t)
     (exit 1)]))
