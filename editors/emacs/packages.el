;;; packages.el --- CaraML layer packages file for Spacemacs.  -*- lexical-binding: t; -*-

;; Author: b4er
;; SPDX-License-Identifier: BSD-3-Clause

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
    :hook (caraml-mode . caraml-eglot-ensure)))

;;; packages.el ends here
