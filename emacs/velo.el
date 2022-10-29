;;; package --- Summary

;;; Commentary:

;; Derived from typos.el and others.

;;; Code:

;; define several class of keywords

(defvar velo-keywords '("fun" "let" "in"))

(defvar velo-types '("nat" "bool"))

(defvar velo-operators '("?"))

(defvar velo-symbols   '(":" "->" "=>" "=" "(" ")"))

(defvar velo-functions '("add" "inc" "the" "and"))

(defvar velo-constants '("true" "false" "zero"))


(defvar velo-font-lock-defaults
  `((
    ( ,(regexp-opt velo-keywords  'words) . font-lock-keyword-face)
    ( ,(regexp-opt velo-types     'words) . font-lock-type-face)
    ( ,(regexp-opt velo-operators 'words) . font-lock-builtin-face)
    ( ,(regexp-opt velo-symbols   'words) . font-lock-builtin-face)
    ( ,(regexp-opt velo-functions 'words) . font-lock-function-name-face)
    ( ,(regexp-opt velo-constants 'words) . font-lock-constant-face)
)))

;;; Clear memory
(setq velo-keywords  nil
      velo-types     nil
      velo-operators nil
      velo-symbols   nil
      velo-functions nil
      velo-constants nil
      )

;; syntax table
(defvar velo-syntax-table nil "Syntax table for `velo-mode'.")
(setq velo-syntax-table
  (let ((synTable (make-syntax-table)))

  ;; comments
  (modify-syntax-entry ?\{  "(}1nb" synTable)
  (modify-syntax-entry ?\}  "){4nb" synTable)
  (modify-syntax-entry ?-  "_ 123" synTable)

  (mapc (lambda (x)
            (modify-syntax-entry x "_" synTable))
          ;; Some of these are actually OK by default.
            "?=:")

  synTable))

(defvar velo-mode-hook nil "Hook for velo-mode.")

;; define the mode
(define-derived-mode velo-mode fundamental-mode
  "Velo mode"

  ;; handling comments
  :syntax-table velo-syntax-table

  ;; syntax highlighting
  (make-local-variable 'velo-font-lock-defaults)
  (make-local-variable 'comment-start)
  (make-local-variable 'comment-end)
  (make-local-variable 'comment-start-skip)
  (make-local-variable 'comment-end-skip)
  (make-local-variable 'comment-column)
  (make-local-variable 'comment-padding)
  (make-local-variable 'comment-multi-line)
  ;;(make-local-variable 'comment-indent-function)

  (setq font-lock-defaults velo-font-lock-defaults
        comment-start           "-- "
        comment-end             ""
        comment-start-skip      "[-{]-[ \t]*"
        comment-end-skip        "[ \t]*\\(-}\\|\\s>\\)"
        comment-column          60
        comment-padding         0
        comment-multi-line      nil
        ;;comment-indent-function 'java-comment-indent
        ;;indent-tabs-mode        t
        )
  (run-hooks 'velo-mode-hook)
)

;; Customisation options

(defgroup velo nil
  "A tiny language (STLC + Hutton's Razor with Bools) to showcase & explore efficient verified implementations in Idris2."
  :group 'languages)

(defcustom velo-command "velo"
  "The path to the Velo command to run."
  :type 'string
  :group 'velo)

(defcustom velo-options nil
  "Command line options to pass to velo."
  :type 'string
  :group 'velo)

(provide 'velo)
;;; velo.el ends here
