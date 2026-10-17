;;; packages.el --- CaraML layer packages file for Spacemacs.  -*- lexical-binding: t; -*-

;; Author: b4er
;; License: same as caraml-mode.el

;;; Commentary:

;; Spacemacs private layer for the CaraML language.  Ships `caraml-mode'
;; as a local package under `local/caraml-mode/'.

;;; Code:

(defconst caraml-packages
  '((caraml-mode :location local)))

(defun caraml/init-caraml-mode ()
  (use-package caraml-mode
    :defer t
    :mode (("\\.caraml\\'" . caraml-mode))
    :hook (caraml-mode . eglot-ensure)))

;;; packages.el ends here
