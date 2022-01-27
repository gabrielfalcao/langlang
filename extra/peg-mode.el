;;; peg-mode.el --- Syntax highlight for Parsing Expression Grammars
;;
;; Copyright (C) 2018-2019  Lincoln Clarete
;;
;; Author: Lincoln de Sousa <lincoln@clarete.li>
;; Version: 0.0.1
;; Homepage: https://github.com/clarete/emacs.d
;;
;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.
;;
;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <https://www.gnu.org/licenses/>.
;;
;;; Commentary:
;;
;; Didn't really find any mode for PEGs that I liked.  Here's what I
;; put together to edit files that follow the syntax that Bryan Ford
;; defined in the paper he introduced PEGs.
;;
;;; Code:


(defconst peg-mode-syntax-table
  (let ((table (make-syntax-table)))
    ;; [] should also look like strings
    (modify-syntax-entry ?\[ "|" table)
    (modify-syntax-entry ?\] "|" table)
    ;; ' is a string delimiter
    (modify-syntax-entry ?' "\"" table)
    ;; " is a string delimiter too
    (modify-syntax-entry ?\" "\"" table)
    ;; Comments start with #
    (modify-syntax-entry ?# "< b" table)
    ;; \n is a comment ender
    (modify-syntax-entry ?\n "> b" table)
    table))


(defvar peg-mode-keywords
  '("lang" "<-" "->"))


(defvar peg-font-lock-defaults
  `((
     ;; keywords
     (,(regexp-opt peg-mode-keywords) . font-lock-keyword-face)
     ;; Color the name of the rule
     ("^\s*\\([a-zA-Z_][a-zA-Z0-9_]*\\)[\s\n:a-zA-Z0-9_]*<-" 1 'font-lock-function-name-face)
     ;; Color for the little assignment arrow
     ("lang\s*\\([a-zA-Z_][a-zA-Z0-9_]*\\)\s*" 1 'font-lock-type-face)
     ;; ! & * + ? ( ) / are operators
     ("!\\|&\\|*\\|+\\|?\\|(\\|)\\|/" . font-lock-builtin-face)
     ;; Color for label
     ("\\(\\^[a-zA-Z_][a-zA-Z0-9_]*\\)" 1 'font-lock-constant-face)
     ;; Color for dotted names
     ("::\\([a-zA-Z_][a-zA-Z0-9_]*\\)" 1 'font-lock-type-face)
     ;; Color for assignment of a name to a piece of the expression.
     ("\\(:[a-zA-Z_][a-zA-Z0-9_]*\\)" 1 'font-lock-variable-name-face))))


(defun peg-mode-indent-line ()
  "Indent current line as PEG code."
  (interactive)
  (beginning-of-line)
  (if (bobp)  ; Check for rule 1
      (indent-line-to 0)
    (let ((not-indented t) cur-indent)
      (if (looking-at "^[ \t]*}")
          (progn
            (save-excursion
              (forward-line -1)
              (setq cur-indent (- (current-indentation) default-tab-width)))
            (if (< cur-indent 0)
                (setq cur-indent 0)))
        (save-excursion
          (while not-indented
            (forward-line -1)
            (if (looking-at "^[ \t]*}") ; Check for rule 3
                (progn
                  (setq cur-indent (current-indentation))
                  (setq not-indented nil))
                                        ; Check for rule 4
              (if (looking-at "^[ \t]*lang[ \t]*[a-zA-Z_][a-zA-Z0-9_]*[ \t]*{")
                  (progn
                    (setq cur-indent (+ (current-indentation) default-tab-width))
                    (setq not-indented nil))
                (if (bobp) ; Check for rule 5
                    (setq not-indented nil)))))))
      (if cur-indent
          (indent-line-to cur-indent)
        (indent-line-to 0))))) ; If we didn't see an indentation hint, then allow no indentation


;;;###autoload
(define-derived-mode peg-mode prog-mode "PEG Mode"
  :syntax-table peg-mode-syntax-table
  (set (make-local-variable 'default-tab-width) 2)
  (set (make-local-variable 'comment-start) "#")
  (set (make-local-variable 'comment-end) "")
  (set (make-local-variable 'font-lock-defaults)
       peg-font-lock-defaults)
  (set (make-local-variable 'indent-line-function)
       'peg-mode-indent-line)
  (font-lock-ensure))

;;;###autoload
(add-to-list 'auto-mode-alist '("\\.peg\\'" . peg-mode))
(add-to-list 'auto-mode-alist '("\\.pegx\\'" . peg-mode))

(provide 'peg-mode)
;;; peg-mode.el ends here
