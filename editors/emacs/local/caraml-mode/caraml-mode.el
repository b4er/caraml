;;; caraml-mode.el --- major mode for the CaraML language -*- lexical-binding: t; -*-

;; Author: b4er
;; SPDX-License-Identifier: BSD-3-Clause
;; Version: 0.0.0
;; Package-Requires: ((emacs "29.1"))
;; Keywords: languages

;;; Commentary:

;; Vanilla Emacs (drop-in via load-path):
;;
;;   (add-to-list 'load-path "/path/to/caraml/editors/emacs/local/caraml-mode")
;;   (require 'caraml-mode)
;;   (add-hook 'caraml-mode-hook #'caraml-eglot-ensure)
;;
;; Spacemacs (private layer):  the enclosing `emacs/' directory *is*
;; the layer -- it already contains `packages.el' and this file under
;; `local/caraml-mode/'.  Symlink it into place once:
;;
;;   ln -s /path/to/caraml/editors/emacs ~/.emacs.d/private/caraml
;;
;; then add `caraml' to `dotspacemacs-configuration-layers' in
;; ~/.spacemacs and restart (or `SPC f e R').  The layer's
;; `packages.el' wires up `auto-mode-alist' and the `eglot-ensure'
;; hook, so no extra user-config is needed.
;;
;; The language server is `caraml lsp'.  When `caraml' is neither on
;; PATH nor in `caraml-server-path', `caraml-eglot-ensure' offers
;; `caraml-setup' (see caraml-setup.el).

;;; Code:

(require 'cl-lib)
(require 'caraml-input)
(require 'caraml-setup)

(defgroup caraml nil
  "Major mode for the CaraML language."
  :group 'languages
  :prefix "caraml-")

;;;; customization -----------------------------------------------------

(define-obsolete-variable-alias 'caraml-lsp-server-path 'caraml-server-path "0.1.0")

(defcustom caraml-server-path nil
  "Path to the caraml executable; Eglot runs it as `caraml lsp'.
Nil looks in $CARAML_SERVER, then PATH, then `caraml-setup-directory'."
  :type '(choice (const :tag "Look it up" nil) file))

(defcustom caraml-server-args nil
  "Global options passed before the `lsp' command, e.g. (\"-vv\") for debug logs.
The log goes to stderr, which Eglot shows in the events buffer."
  :type '(repeat string))

(defcustom caraml-use-input-method t
  "Turn on the `caraml' input method in CaraML buffers.
It replaces backslash abbreviations as you type: `\\alpha' becomes `α',
`\\to' becomes `→' (the canonical arrow), `\\le' becomes `≤'.  Toggle it
in a buffer with \\[toggle-input-method]."
  :type 'boolean)

(defcustom caraml-indent-offset 2
  "Number of columns per indentation level."
  :type 'integer)

(declare-function eglot-current-server "eglot")
(declare-function jsonrpc-notify "jsonrpc")

(defun caraml--set-and-notify (sym val)
  "Set SYM to VAL and send the new settings to running CaraML servers.
Runs for `customize' and `setopt', not for a plain `setq'."
  (set-default sym val)
  (when (featurep 'eglot)
    (let (seen)
      (dolist (buf (buffer-list))
        (with-current-buffer buf
          (when-let* (((derived-mode-p 'caraml-mode))
                      (srv (eglot-current-server))
                      ((not (memq srv seen))))
            (push srv seen)
            (jsonrpc-notify srv :workspace/didChangeConfiguration
                            (list :settings (caraml--lsp-initialization-options)))))))))

(defcustom caraml-inlay-hints-enabled nil
  "Show inferred type hints inline after value bindings.
Mirrors `caraml.inlayHints.enabled' from ../vscode/."
  :type 'boolean
  :set #'caraml--set-and-notify)

(defcustom caraml-inlay-hints-literals nil
  "Also annotate bindings whose value is an obvious literal.
Mirrors `caraml.inlayHints.literals' from ../vscode/."
  :type 'boolean
  :set #'caraml--set-and-notify)

(defcustom caraml-inlay-hints-hide-type-variables t
  "Suppress hints whose inferred type is an unsolved type variable.
Mirrors `caraml.inlayHints.hideTypeVariables' from ../vscode/."
  :type 'boolean
  :set #'caraml--set-and-notify)

;;;; syntax table ------------------------------------------------------

(eval-and-compile
  (defconst caraml--op-chars "!#$%&*+/:<=>?@^|~\u2190-\u22ff-"
    "Operator characters, for a regexp bracket: ASCII symbols, arrows and
mathematical operators (U+2190..U+22FF), as in ../vscode/."))

;; A single `-' character cannot carry both style-A (for `--') and
;; style-B (for `{-') comment position flags via `modify-syntax-entry',
;; so `-' is punctuation here and comment fences are installed via
;; `syntax-propertize-function' below.

(defvar caraml-mode-syntax-table
  (let ((table (make-syntax-table)))
    (modify-syntax-entry ?\( "()"  table)
    (modify-syntax-entry ?\) ")("  table)
    (modify-syntax-entry ?\[ "(]"  table)
    (modify-syntax-entry ?\] ")["  table)
    (modify-syntax-entry ?\{ "(}"  table)
    (modify-syntax-entry ?\} "){"  table)
    (modify-syntax-entry ?\" "\""  table)
    (modify-syntax-entry ?\\ "."   table)     ; literals admit no escapes
    (modify-syntax-entry ?_  "_"   table)
    (modify-syntax-entry ?'  "_"   table)
    (modify-syntax-entry ?\n ">"   table)     ; ends style-A line comments
    (dolist (c '(?! ?# ?$ ?% ?& ?* ?+ ?- ?/ ?: ?< ?= ?> ?? ?@ ?^ ?| ?~))
      (modify-syntax-entry c "."   table))
    (modify-syntax-entry '(#x2190 . #x22ff) "." table)
    table)
  "Syntax table for `caraml-mode'.")

(defvar caraml--syntax-propertize
  (syntax-propertize-rules
   ;; Line comment: two or more dashes NOT continued into an operator
   ;; run (--> and -< are operators, not comment starters).
   ((concat "\\(-\\)-+\\(?:[^" caraml--op-chars "]\\|$\\)")
    (1 "<"))
   ;; A character literal holding a quote or bracket must not open a
   ;; string or a paren.
   ("\\(?:^\\|[^[:alnum:]_']\\)'\\([^'[:alnum:]_ ]\\)'"
    (1 "."))
   ;; Nested block comment fences.
   ("\\({\\)-"    (1 "< bn"))
   ("-\\(}\\)"    (1 "> bn"))))

;;;; font lock ---------------------------------------------------------

(defconst caraml--keywords-control
  '("if" "else" "match" "handle" "handler" "mask" "return" "finally"
    "let" "fn" "as"))

(defconst caraml--keywords-declaration
  '("type" "module" "signature" "implicit" "instance" "open" "include"
    "extern" "effect" "protocol" "infix" "infixl" "infixr"))

(defconst caraml--reserved-operators '("->" "→" "<-" "←" "=" ":" "|")
  "Operator runs that are syntax, not user operators.")

(defface caraml-reserved-operator-face
  '((t :inherit font-lock-keyword-face))
  "Face for the reserved operators in `caraml--reserved-operators'.")

(defvar caraml-font-lock-keywords
  `((,(regexp-opt caraml--keywords-control    'symbols) . font-lock-keyword-face)
    (,(regexp-opt caraml--keywords-declaration 'symbols) . font-lock-keyword-face)
    ("\\(?:^\\|[^[:alnum:]_']\\)\\('[^']'\\)"           1 font-lock-constant-face)
    ("\\_<[[:upper:]][[:alnum:]_']*\\_>"                 . font-lock-type-face)
    ("\\_<[0-9]+\\_>"                                    . font-lock-constant-face)
    (,(concat "[" caraml--op-chars "]+")
     (0 (if (member (match-string 0) caraml--reserved-operators)
            'caraml-reserved-operator-face
          'font-lock-builtin-face)))
    ("\\_<_\\_>"                                         . font-lock-variable-name-face)))

;;;; indentation -------------------------------------------------------

(defconst caraml--increase-indent-re
  "\\(?:=\\|<-\\|←\\|->\\|→\\|(\\|\\[\\|{\\)[ \t]*\\(?:--.*\\)?$")

(defconst caraml--decrease-indent-re
  "^[ \t]*[]})]")

(defun caraml--previous-code-line ()
  "Return (INDENT . TEXT) of the previous non-blank, non-comment line, or nil."
  (save-excursion
    (forward-line -1)
    (while (and (not (bobp))
                (or (looking-at-p "\\s-*$")
                    (nth 4 (syntax-ppss (line-beginning-position)))))
      (forward-line -1))
    (unless (and (bobp) (looking-at-p "\\s-*$"))
      (cons (current-indentation)
            (buffer-substring-no-properties
             (line-beginning-position) (line-end-position))))))

(defun caraml-indent-line ()
  "Indent the current line for `caraml-mode'."
  (interactive)
  (let* ((prev (caraml--previous-code-line))
         (base (if prev (car prev) 0))
         (cur  (buffer-substring-no-properties
                (line-beginning-position) (line-end-position))))
    (when (and prev (string-match-p caraml--increase-indent-re (cdr prev)))
      (setq base (+ base caraml-indent-offset)))
    (when (string-match-p caraml--decrease-indent-re cur)
      (setq base (max 0 (- base caraml-indent-offset))))
    (if (<= (current-column) (current-indentation))
        (indent-line-to base)
      (save-excursion (indent-line-to base)))))

(defun caraml--lsp-initialization-options ()
  "Assemble the `initializationOptions' plist sent to `caraml lsp'.
Shape matches what ../vscode/src/extension.ts sends."
  `(:inlayHints
    ( :enabled           ,(if caraml-inlay-hints-enabled           t :json-false)
      :literals          ,(if caraml-inlay-hints-literals          t :json-false)
      :hideTypeVariables ,(if caraml-inlay-hints-hide-type-variables t :json-false))))

(with-eval-after-load 'eglot
  (defclass caraml-eglot-server (eglot-lsp-server) ()
    :documentation "Eglot server class for `caraml lsp'.")

  (cl-defmethod eglot-initialization-options ((_srv caraml-eglot-server))
    (caraml--lsp-initialization-options))

  (defun caraml--eglot-contact (_interactive)
    "Return the Eglot server-contact list for `caraml-mode'."
    `(caraml-eglot-server ,(or (caraml-server) "caraml") ,@caraml-server-args "lsp"))

  (add-to-list 'eglot-server-programs
               '(caraml-mode . caraml--eglot-contact)))

(defun caraml-restart-server ()
  "Restart the CaraML language server for the current buffer."
  (interactive)
  (unless (fboundp 'eglot-reconnect)
    (user-error "Eglot not available; require Emacs 29+ or load Eglot"))
  (call-interactively #'eglot-reconnect))

;;;; mode --------------------------------------------------------------

(defvar caraml-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd "C-c C-r") #'caraml-restart-server)
    map)
  "Keymap for `caraml-mode'.")

;;;###autoload
(define-derived-mode caraml-mode prog-mode "CaraML"
  "Major mode for editing CaraML source files."
  :syntax-table caraml-mode-syntax-table
  (setq-local comment-start "-- ")
  (setq-local comment-end   "")
  (setq-local comment-start-skip "\\(?:--+\\|{-\\)[ \t]*")
  (setq-local comment-end-skip   "[ \t]*\\(?:\n\\|-}\\)")
  (setq-local parse-sexp-ignore-comments t)
  (setq-local syntax-propertize-function caraml--syntax-propertize)
  (setq-local font-lock-defaults '(caraml-font-lock-keywords))
  (setq-local indent-line-function #'caraml-indent-line)
  (setq-local indent-tabs-mode nil)
  (when caraml-use-input-method
    (activate-input-method "caraml")))

;;;###autoload
(add-to-list 'auto-mode-alist '("\\.caraml\\'" . caraml-mode))

;; `caraml lsp' returns hover payloads as markdown with ```caraml fences.
;; Teach `markdown-mode' to fontify those blocks with our mode.
(defvar markdown-code-lang-modes)
(with-eval-after-load 'markdown-mode
  (add-to-list 'markdown-code-lang-modes '("caraml" . caraml-mode)))

(provide 'caraml-mode)
;;; caraml-mode.el ends here
