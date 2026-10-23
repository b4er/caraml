<div align="center">
  <img src="./web/assets/caraml-logo.svg" width="260" alt="CaraML">

  <h3>A strict functional language in the ML family,<br>with a compiler verified in Isabelle/HOL.</h3>

  [![CI/CD](https://github.com/b4er/caraml-test/actions/workflows/cicd.yaml/badge.svg?branch=main)](https://github.com/b4er/caraml-test/actions/workflows/cicd.yaml)
  [![Release](https://img.shields.io/github/v/release/b4er/caraml-test)](https://github.com/b4er/caraml-test/releases/latest)
  [![License](https://img.shields.io/badge/license-BSD--3--Clause-blue)](LICENSE)

  [Website](https://b4er.github.io/caraml-test/) |
  [Releases](https://github.com/b4er/caraml-test/releases)
</div>

---

## Why CaraML?

- **Formally verified:** Machine-checked in Isabelle/HOL: well-typed programs
  never crash, and compilation preserves I/O behaviour down to the target code.
- **Total by default:** Function types carry their (named) effects - no unstated
  side-effects. Divergence is an effect too, so a pure type means a total
  function.
- **Multi-shot handlers:** A `handler` clause binds the resumption as an
  ordinary value. Call it once, many times, or never.
- **Modular implicits:** Interfaces are signatures, instances are modules,
  nothing is canonical. Implicit arguments are elaborated from the instances in
  scope.
- **Statically interpreted modules:** ML signatures, functors and sealing,
  compiled away by static interpretation. Expressive abstraction without runtime
  indirection.
- **Recursion schemes:** Every `type` gets an `Inductive` instance from the
  compiler: a generic fold, with termination for free.
- **Layout syntax:** UTF-8 source, user-defined operators, blocks by braces or
  by indentation. No preprocessor, no fixity tables.
- **Separate compilation:** One file compiles to one module. Modules link after
  compilation, nothing is recompiled twice.

## Quick start

Install your editor plugin, open a `.caraml` file and follow the dialog to
install the compiler (either download from release, or build from sources).

### VSCode / VSCodium

Install the extension from either

- [`b4er.caraml`](https://marketplace.visualstudio.com/items?itemName=b4er.caraml) (Visual Studio Marketplace), or
- [`b4er.caraml`](https://open-vsx.org/extension/ms-python/python) (Open VSX Registry).

### Spacemacs

In `~/.spacemacs`, fetch the mode from git in
`dotspacemacs-additional-packages`:

```elisp
(caraml-mode :location (recipe :fetcher github :repo "b4er/caraml"
                               :files ("editors/emacs/local/caraml-mode/*.el")))
```

and start the language server in `dotspacemacs/user-config`:

```elisp
(add-hook 'caraml-mode-hook #'caraml-eglot-ensure)
```

### Emacs

Requires Emacs 29.1 or later (for Eglot). With Emacs 30, in your `init.el`:

```elisp
(use-package caraml-mode
  :vc (:url "https://github.com/b4er/caraml"
       :lisp-dir "editors/emacs/local/caraml-mode")
  :hook (caraml-mode . caraml-eglot-ensure))
```

With Emacs 29, install once with `M-x eval-expression`:

```elisp
(package-vc-install
 '(caraml-mode :url "https://github.com/b4er/caraml"
               :lisp-dir "editors/emacs/local/caraml-mode"))
```

and add `(add-hook 'caraml-mode-hook #'caraml-eglot-ensure)` to your `init.el`.

## Overview

```console
git clone --recursive https://github.com/b4er/caraml.git && cd caraml
```

This repository contains the Isabelle formalization split across the following
roots:

<div align="center">
  
| | |
|-|-|
| [`prelude/`](prelude) | Shared Isabelle library (predictable, named cases) |
| [`spec/`](spec) | Abstract compiler specification (program refinement and separate compilation) |
| [`syntax/`](syntax) | The abstract syntax for (module) expressions |
| [`parser/`](parser) | Surface grammar and generated parser |
| [`core/`](core) | Core calculus |
| [`typing/`](typing) | Type checking and inference |
| [`haskell/`](haskell) | Code exports |
| [`web/`](web) | Static website |

</div>

You'll need [Isabelle2025-2](https://isabelle.in.tum.de/), the
[AFP](https://www.isa-afp.org/download/) (release `2026-07-21`) to generate the
verified code (writes to `haskell/verified`):

```console
isabelle build -bed . CaraML_Export
```

The verified Haskell code is wrapped by the project in
[`haskell/caraml.cabal`](haskell/caraml.cabal) and can be installed with Cabal:

```console
cabal install --project-dir=haskell/ exe:caraml
```

The executable provides a language server which can be used by the editor
plugins implemented in [`editors/`](editors).

## License

CaraML is distributed under the [BSD 3-Clause License](LICENSE).