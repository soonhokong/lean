;; Copyright (c) 2014 Microsoft Corporation. All rights reserved.
;; Released under Apache 2.0 license as described in the file LICENSE.
;;
;; Author: Soonho Kong
;;
(require 'package)

(defvar lean-mode-required-packages
  '(company dash dash-functional flycheck f fill-column-indicator s lua-mode mmm-mode))

(defun lean-setup-required-packages ()
  "Install required/optional packages for lean-mode "
  (let ((uninstalled-packages
         (--filter (not (package-installed-p it))
                   lean-mode-required-packages)))
    (when uninstalled-packages
      (add-to-list 'package-archives '("gnu" . "http://elpa.gnu.org/packages/") t)
      (add-to-list 'package-archives '("melpa" . "http://melpa.milkbox.net/packages/") t)
      (package-initialize)
      (package-refresh-contents)
      (--map (package-install it) uninstalled-packages))))

(defun lean-mode-require-package (pkg)
  "Check whether pkg is available or not."
  (unless (featurep pkg)
    (if (not (require pkg (symbol-name pkg) t))
        (error "lean-mode: required package '%s' is not found." (symbol-name pkg))
      (message "lean-mode: package %S loaded." pkg))))

(defun lean-mode-check-package (pkg)
  "Check whether pkg is available or not."
  (unless (featurep pkg)
    (if (not (require pkg (symbol-name pkg) t))
        (message "lean-mode: optional package '%s' is not found." (symbol-name pkg))
      (message "lean-mode: optional package %S loaded." pkg))))

(defun lean-mode-check-requirements ()
  "Check lean-mode requirements"
  (if (not (>= emacs-major-version 24))
      (error "Emacs version >= 24 is required to use lean-mode"))
  (lean-mode-check-package 'package)
  (lean-mode-check-package 'dash)
  (let ((required-packages '(cl-lib compile dash dash-functional f flymake s))
        (optional-packages '(flycheck fill-column-indicator lua-mode mmm-mode)))
    (-each required-packages 'lean-mode-require-package)
    (-each optional-packages 'lean-mode-check-package)))

(lean-mode-check-requirements)
(provide 'lean-require)
