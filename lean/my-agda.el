;;; Maps C-c C-<key> to \<key in evil-normal-state
(eval-after-load 'agda2
  '(progn
     (evil-define-key 'normal agda2-mode-map
       "\\a" 'agda2-auto
       "\\k" 'agda2-previous-goal
       "\\j" 'agda2-next-goal
       "\\c" 'agda2-make-case
       "\\d" 'agda2-infer-type-maybe-toplevel
       "\\e" 'agda2-show-context
       "\\l" 'agda2-load
       "\\n" 'agda2-compute-normalised-maybe-toplevel
       "\\o" 'agda2-module-contents-maybe-toplevel
       "\\r" 'agda2-refine
       "\\s" 'agda2-solveAll
       "\\t" 'agda2-goal-type
       "\\ " 'agda2-give
       "\\," 'agda2-goal-and-context
       "\\." 'agda2-goal-and-context-and-inferred
       "\\=" 'agda2-show-constraints
       "\\?" 'agda2-show-goals
       "\\xc" 'agda2-compile
       "\\xd" 'agda2-remove-annotations
       "\\xh" 'agda2-display-implicit-arguments
       "\\xl" 'agda2-load
       "\\xq" 'agda2-quit
       "\\xr" 'agda2-restart)))

;;; Set up unicode input
(add-hook 'evil-insert-state-entry-hook (lambda () (set-input-method "Agda")))
(add-hook 'evil-insert-state-exit-hook (lambda () (set-input-method nil)))
