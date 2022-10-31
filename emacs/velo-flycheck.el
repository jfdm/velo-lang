;;; package --- Summary

;;; Commentary:

;;; Code:

;; define several class of keywords

(require 'velo)
(require 'flycheck)

(flycheck-def-executable-var
 flycheck-velo
 velo-command
 )

;; TODO
;;(flycheck-def-option-var
;;    flycheck-velo-opts
;;    '(velo-options)
;;    velo
;;    "Options")

(flycheck-define-checker velo
  "A linter for Velo"
  :command ("velo" "--checkOnly"
            (source ".velo"))
  :error-patterns
  ((error line-start
          (file-name) ":" line ":" column "-" end-column ":\n"
          (message (and (* nonl) (* "\n" (* nonl))))
          )
   )

  :modes velo-mode
  )
(add-to-list 'flycheck-checkers 'velo)

(provide 'velo-flycheck)
;;; velo-flycheck.el ends here

;;;(flycheck-parse-error-with-patterns
;;; "test.velo:13:1-2:\nsksksk"
;;; (flycheck-checker-get 'velo 'error-patterns)
;;; 'velo-check)
