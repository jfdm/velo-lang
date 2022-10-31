(load "$HOME/project/velo/velo-lang/emacs/velo.el")
(load "$HOME/project/velo/velo-lang/emacs/velo-flycheck.el")
(require 'velo)
(require 'velo-flycheck)

(flycheck-parse-error-with-patterns
 "poo.velo:13:1-2:[ ERROR ]\nsksksk"
 (flycheck-checker-get 'velo-check 'error-patterns)
 'velo-check)
