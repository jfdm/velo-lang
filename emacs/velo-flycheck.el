;;; package --- Summary

;;; Commentary:

;;; Code:

;; define several class of keywords

(require 'velo)
(require 'flycheck)

(flycheck-def-executable-var
 flycheck-velo-check
 velo-command
 )

;;(flycheck-def-option-var
;;    flycheck-velo-opts
;;    '(velo-options)
;;    velo-check
;;    "Options")

(flycheck-define-checker velo-check
  "A linter for Velo"
  :command ("velo" "--checkOnly"
            (source ".velo"))
  :error-patterns
  (;(error line-start
   ;       "[ ERROR ] "
   ;       (file-name) ":" line ":" column "-" end-column ":"
   ;       (message)
   ;
   ;       )
   (error line-start "[ ERROR ] " (file-name) ":" line ":" column "-" end-column ":"
          (message (and (* nonl) (* "\n" (* nonl)))))
   )

  :modes velo-mode
  )
(add-to-list 'flycheck-checkers 'velo-check)

(provide 'velo-flycheck)
;;; velo-flycheck.el ends here
