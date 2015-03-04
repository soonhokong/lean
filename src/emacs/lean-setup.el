;; Copyright (c) 2015, Soonho Kong. All rights reserved.
;; Released under Apache 2.0 license as described in the file LICENSE.
;;
;; Author: Soonho Kong
;;

(require 'package)
(add-to-list 'package-archives '("gnu" . "http://elpa.gnu.org/packages/") t)
(add-to-list 'package-archives '("melpa" . "http://melpa.milkbox.net/packages/") t)
(package-initialize)
(defvar lean-mode-required-packages
  '(company dash dash-functional flycheck f fill-column-indicator s lua-mode mmm-mode))

;; Install required/optional packages for lean-mode
(let ((uninstalled-packages
       (--filter (not (package-installed-p it))
                 lean-mode-required-packages)))
  (when uninstalled-packages
    (package-refresh-contents)
    (--map (package-install it) uninstalled-packages)))

(require 'f)
(require 'dash)
;; Set up lean-rootdir
(if (or (not (boundp 'lean-rootdir))
        (not lean-rootdir))
    (let* ((candidates
          '("/usr" "/usr/local" "/opt/local" "~/work/lean"))
         (filtered-candidates
          (--filter (f-exists? (f-join it "bin" "lean")) candidates))
         (candidate (-first-item filtered-candidates)))
    (unless candidate
      (user-error "%S is not set, and we cannot find it from pre-defined candidate locations: %S"
                  'lean-root-dir
                  candidates))
    (setq lean-rootdir candidate)))

;; Set up lean-emacs-path
(if (or (not (boundp 'lean-emacs-path))
        (not lean-emacs-path))
  (let* ((candidate-postfixes
          `(,(f-join "src" "emacs")
            ,(f-join "share" "emacs" "site-lisp" "lean")))
         (candidates (--map (f-join lean-rootdir it) candidate-postfixes))
         (filtered-candidates
          (-filter 'f-exists? candidates))
         (candidate (-first-item filtered-candidates)))
    (unless candidate
      (user-error "%S is not set, and we cannot find it from pre-defined candidate locations: %S"
                  'lean-emacs-path
                  candidates))
    (setq lean-emacs-path candidate)))

;; Require lean-mode
(when (and lean-rootdir lean-emacs-path)
  (add-to-list 'load-path (expand-file-name lean-emacs-path))
  (require 'lean-mode))
