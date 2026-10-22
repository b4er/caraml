;;; caraml-setup.el --- find or install the CaraML language server -*- lexical-binding: t; -*-

;; Author: b4er
;; SPDX-License-Identifier: BSD-3-Clause

;;; Commentary:

;; find the caraml executable, set it up when it is missing.
;;
;; release CI publishes under the tag `v<version>` of the extension version
;;   caraml-<version>-<platform>-<arch>.tar.gz   (pre-built, `caraml` or `caraml.exe` inside)
;;   caraml-<version>.tar.gz                     (`cabal sdist` of haskell/)
;; with <platform>-<arch> as Node names them: linux-x64, darwin-arm64, win32-x64, ...

;;; Code:

(require 'cl-lib)
(require 'seq)
(require 'subr-x)
(require 'url)

(defvar caraml-server-path)
(defvar url-http-response-status)
(defvar url-http-end-of-headers)

(defconst caraml-version "0.1.0"
  "Version of the server this mode expects; keep in sync with the package.")

(defconst caraml--repo "b4er/caraml")

(defconst caraml--exe (if (eq system-type 'windows-nt) "caraml.exe" "caraml"))

(defcustom caraml-setup-prompt t
  "Offer to set up the server when a CaraML buffer finds none."
  :type 'boolean
  :group 'caraml)

(defcustom caraml-setup-directory (locate-user-emacs-file "caraml/")
  "Directory for downloaded and built servers."
  :type 'directory
  :group 'caraml)

(defun caraml--installed ()
  "The server under `caraml-setup-directory' for `caraml-version'."
  (expand-file-name (concat "server/" caraml-version "/bin/" caraml--exe)
                    caraml-setup-directory))

(defun caraml-server ()
  "The caraml executable: `caraml-server-path', $CARAML_SERVER, PATH,
then `caraml-setup-directory'.  Nil when there is none."
  (or caraml-server-path
      (getenv "CARAML_SERVER")
      (executable-find "caraml")
      (let ((f (caraml--installed)))
        (and (file-executable-p f) f))))

(defvar caraml--setup-offered nil
  "Non-nil once this session offered the setup.")

;;;###autoload
(defun caraml-eglot-ensure ()
  "Start Eglot when the server exists, otherwise offer `caraml-setup'.
Use it in `caraml-mode-hook' in place of `eglot-ensure'."
  (cond ((caraml-server) (eglot-ensure))
        ((and caraml-setup-prompt (not caraml--setup-offered))
         (setq caraml--setup-offered t)
         ;; after the buffer shows, not inside `find-file'
         (run-at-time 0 nil #'caraml-setup 'offer))))

;;;; wizard ------------------------------------------------------------

(defun caraml--target ()
  "<platform>-<arch> as Node names them."
  (format "%s-%s"
          (pcase system-type
            ('gnu/linux "linux") ('darwin "darwin") ('windows-nt "win32")
            (_ system-type))
          (pcase (car (split-string system-configuration "-"))
            ("x86_64" "x64") ((or "aarch64" "arm64") "arm64")
            (arch arch))))

(defun caraml--find-release ()
  "The GitHub release for `caraml-version', else the latest, else nil."
  (cl-loop
   for which in (list (concat "tags/v" caraml-version) "latest")
   thereis
   (ignore-errors
     (let ((url-request-extra-headers '(("Accept" . "application/vnd.github+json")))
           (buf (url-retrieve-synchronously
                 (format "https://api.github.com/repos/%s/releases/%s" caraml--repo which)
                 t nil 10)))
       (unwind-protect
           (with-current-buffer buf
             (when (eq url-http-response-status 200)
               (goto-char url-http-end-of-headers)
               (json-parse-buffer :object-type 'alist :array-type 'list)))
         (kill-buffer buf))))))

(defun caraml--asset (release name)
  "Download URL of the asset NAME in RELEASE, or nil."
  (cl-loop for a in (alist-get 'assets release)
           when (equal (alist-get 'name a) name)
           return (alist-get 'browser_download_url a)))

(defun caraml--tool-version (tool)
  "Output of TOOL --numeric-version, or nil."
  (when (executable-find tool)
    (car (ignore-errors (process-lines tool "--numeric-version")))))

(defun caraml-setup (&optional offer)
  "Set up the CaraML language server.
With OFFER, as when a CaraML buffer finds no server, also offer to
postpone or stop asking."
  (interactive)
  (let* ((target (caraml--target))
         (release (progn (message "CaraML: looking for a server...")
                         (caraml--find-release)))
         (tag (alist-get 'tag_name release))
         (cabal (caraml--tool-version "cabal"))
         (ghc (caraml--tool-version "ghc"))
         (cabal-ok (and cabal (>= (string-to-number cabal) 3)))
         (binary (caraml--asset release (format "caraml-%s-%s.tar.gz" caraml-version target)))
         (sdist (caraml--asset release (format "caraml-%s.tar.gz" caraml-version)))
         (releases (format "https://github.com/%s/releases" caraml--repo))
         (ghcup "https://www.haskell.org/ghcup/")
         ;; (label run-or-nil reason help)
         (choices
          `(("Download a pre-built server"
             ,(and binary (lambda () (caraml--fetch-binary binary)))
             ,(if release
                  (format "release %s has no pre-built server for %s" tag target)
                (format "no release of caraml %s could be reached" caraml-version))
             ,releases)
            ("Build from source"
             ,(and sdist cabal-ok ghc (lambda () (caraml--build sdist)))
             ,(cond ((not sdist)
                     (format "no source release of caraml %s could be reached" caraml-version))
                    ((not cabal-ok)
                     (if cabal (format "building needs cabal 3 or later, found cabal %s" cabal)
                       "building needs cabal 3 or later on PATH"))
                    (t "building needs ghc on PATH"))
             ,ghcup)
            ("Locate an installed caraml" caraml--locate)
            ,@(when offer
                '(("Not now" ignore)
                  ("Don't ask again" caraml--dismiss)))))
         (choices (append (seq-filter #'cadr choices) (seq-remove #'cadr choices)))
         (details
          `(("Download a pre-built server" . ,(and binary (format "caraml %s for %s" tag target)))
            ("Build from source" . ,(and cabal-ok ghc (format "cabal %s, ghc %s; takes several minutes" cabal ghc)))
            ("Locate an installed caraml" . "sets caraml-server-path")))
         (completion-extra-properties
          `(:annotation-function
            ,(lambda (label)
               (let ((c (assoc label choices)))
                 (if (cadr c)
                     (when-let* ((d (alist-get label details nil nil #'equal)))
                       (format "  (%s)" d))
                   (format "  [unavailable: %s]" (nth 2 c)))))))
         (pick (assoc (completing-read
                       (if offer "CaraML server not found; set it up: " "Set up the CaraML server: ")
                       choices nil t)
                      choices)))
    (cond ((cadr pick) (funcall (cadr pick)))
          ((y-or-n-p (format "Unavailable: %s.  Open %s? " (nth 2 pick) (nth 3 pick)))
           (browse-url (nth 3 pick))))))

(defun caraml--dismiss ()
  (setq caraml-setup-prompt nil)
  (kill-new "(setq caraml-setup-prompt nil)")
  (message "CaraML: to stop asking for good, add the copied line to your init file (dotspacemacs/user-config)"))

(defun caraml--locate ()
  (let ((file (read-file-name "caraml executable: " nil nil t)))
    (setq caraml-server-path (expand-file-name file))
    (kill-new (format "(setq caraml-server-path %S)" caraml-server-path))
    (caraml--connect)
    (message "CaraML: using %s; to keep it, add the copied line to your init file (dotspacemacs/user-config)"
             caraml-server-path)))

(defun caraml--connect ()
  "Connect every CaraML buffer; each does so on its next command."
  (dolist (buf (buffer-list))
    (with-current-buffer buf
      (when (derived-mode-p 'caraml-mode)
        (eglot-ensure)))))

(defun caraml--unpack (url)
  "Download the .tar.gz at URL and unpack it into a fresh directory; return it."
  (let* ((dir (expand-file-name (concat "server/" caraml-version "/") caraml-setup-directory))
         (name (file-name-nondirectory url))
         (out (expand-file-name (string-remove-suffix ".tar.gz" name) dir))
         (archive (expand-file-name name dir)))
    (delete-directory out t)
    (make-directory out t)
    (message "CaraML: downloading %s..." name)
    (url-copy-file url archive t)
    (unwind-protect
        (unless (eq 0 (call-process "tar" nil nil nil "-xzf" archive "-C" out))
          (error "Unpacking %s failed" name))
      (delete-file archive))
    out))

(defun caraml--fetch-binary (url)
  (let* ((out (caraml--unpack url))
         (file (car (directory-files-recursively out (concat "\\`" (regexp-quote caraml--exe) "\\'"))))
         (dest (caraml--installed)))
    (unless file
      (error "%s contains no %s" (file-name-nondirectory url) caraml--exe))
    (make-directory (file-name-directory dest) t)
    (rename-file file dest t)
    (set-file-modes dest #o755)
    (delete-directory out t)
    (caraml--connect)
    (message "CaraML: installed %s" dest)))

(defun caraml--build (url)
  (let* ((out (caraml--unpack url))
         ;; a cabal sdist unpacks to <package>-<version>/
         (src (expand-file-name (file-name-nondirectory out) out))
         (default-directory (file-name-as-directory (if (file-directory-p src) src out)))
         (bin (file-name-directory (caraml--installed)))
         (buf (get-buffer-create "*caraml-setup*")))
    (with-current-buffer buf
      (erase-buffer)
      (special-mode))
    (display-buffer buf)
    (make-process
     :name "caraml-setup"
     :buffer buf
     :command (list "cabal" "install" "exe:caraml"
                    (concat "--installdir=" bin) "--install-method=copy"
                    "--overwrite-policy=always")
     :filter (lambda (proc s)
               (with-current-buffer (process-buffer proc)
                 (let ((inhibit-read-only t))
                   (goto-char (point-max))
                   (insert s))))
     :sentinel (lambda (proc _)
                 (when (memq (process-status proc) '(exit signal))
                   (if (eq 0 (process-exit-status proc))
                       (progn (caraml--connect)
                              (message "CaraML: built %s" (caraml--installed)))
                     (message "CaraML: cabal install failed, see *caraml-setup*")))))
    (message "CaraML: building with cabal, see *caraml-setup*")))

(provide 'caraml-setup)
;;; caraml-setup.el ends here
