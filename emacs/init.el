(custom-set-variables
  ;; custom-set-variables was added by Custom.
  ;; If you edit it by hand, you could mess it up, so be careful.
  ;; Your init file should contain only one such instance.
  ;; If there is more than one, they won't work right.
 '(delete-selection-mode t nil (delsel))
 '(inhibit-startup-screen t)
 '(use-dialog-box nil))

(custom-set-faces
  ;; custom-set-faces was added by Custom.
  ;; If you edit it by hand, you could mess it up, so be careful.
  ;; Your init file should contain only one such instance.
  ;; If there is more than one, they won't work right.
 )

;; Shorter prompts
(fset 'yes-or-no-p 'y-or-n-p)

;; Set filename coding system
(set-file-name-coding-system 'utf-8)

(tool-bar-mode -1)

(require 'package)
(add-to-list 'package-archives '("melpa" . "http://melpa.milkbox.net/packages/") t)
(when (< emacs-major-version 24)
  ;; For important compatibility libraries like cl-lib
  (add-to-list 'package-archives '("gnu" . "http://elpa.gnu.org/packages/")))
(package-initialize)


;(add-to-list 'custom-theme-load-path "~/.emacs.d/themes/")
;(load-theme 'jbeans t)

;(require 'evil)
;(evil-mode 1)

(add-to-list 'load-path "/usr/share/emacs/site-lisp/tex-utils")
;;(require 'xdvi-search)

(load "/home/stephen/.emacs.d/my-agda.el")
(load "/home/stephen/.emacs.d/my-lean.el")
