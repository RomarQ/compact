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

(library (save-normalized-ir-passes)
  (export save-normalized-ir-passes)
  (import (except (chezscheme) errorf)
          (utils)
          (nanopass)
          (langs)
          (vm)
          (compiler-version)
          (language-version)
          (runtime-version)
          (pass-helpers))

  (include "save-normalized-ir-passes/extract-normalized-ir.ss")

  (include "save-normalized-ir-passes/save-normalized-ir.ss")

  (define-passes save-normalized-ir-passes
    (save-normalized-ir              Lloweredemit))
)
