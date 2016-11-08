;; Install required/optional packages for lean-mode
(defvar lean-mode-required-packages
  '(company dash dash-functional flycheck f
            fill-column-indicator s))
(let ((need-to-refresh t))
  (dolist (p lean-mode-required-packages)
    (when (not (package-installed-p p))
      (when need-to-refresh
        (package-refresh-contents)
        (setq need-to-refresh nil))
      (package-install p))))

;; Set up lean-root path
(setq lean-rootdir "~/src/lean")  ;; <=== YOU NEED TO MODIFY THIS
(setq-local lean-emacs-path
  (concat (file-name-as-directory lean-rootdir)
    (file-name-as-directory "src")
    "emacs"))
(add-to-list 'load-path (expand-file-name lean-emacs-path))
(require 'lean-mode)

;; Set up agda-input
(require 'agda-input)
(add-hook 'evil-insert-state-entry-hook (lambda () (set-input-method "Agda")))
(add-hook 'evil-insert-state-exit-hook (lambda () (set-input-method nil)))

(eval-after-load 'lean-mode
  '(progn
     (evil-define-key 'normal lean-mode-map
       "\\x" 'lean-std-exe
       "\\l" 'lean-std-exe
       "\\k" 'quail-show-key
       "\\o" 'lean-set-option
       "\\e" 'lean-eval-cmd
       "\\t" 'lean-show-type
       "\\f" 'lean-fill-placeholder
       "\\r" 'lean-server-restart-process
       "\\g" 'lean-show-goal-at-pos
       "\\p" 'lean-show-id-keyword-info)))
