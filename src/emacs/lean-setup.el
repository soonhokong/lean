;; Copyright (c) 2015, Soonho Kong. All rights reserved.
;; Released under Apache 2.0 license as described in the file LICENSE.
;;
;; Author: Soonho Kong
;;

;; Require lean-mode
(when (and lean-rootdir lean-emacs-path)
  (add-to-list 'load-path (expand-file-name lean-emacs-path))
  (require 'lean-mode))
