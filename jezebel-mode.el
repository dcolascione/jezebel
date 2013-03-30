;;; Mode support functions for jezebel
(require 'jezebel-engine)
(require 'jezebel-grammar)

;;
;; The buffer changes. We get a before-change-hook, and store the
;; dirty region information for after-change-hook. We mark our global
;; AST dirty.
;; 
;; Then, font-lock does its thing and asks us to expand the
;; after-change region. Here, we build a new AST for the current
;; buffer (because we marked the current AST dirty), reusing as much
;; of the old AST as possible. We mark the nodes that have changed in
;; the new AST relative to the old AST and report to font-lock the
;; smallest region that encloses the dirty parts of the new AST.
;;
;; Then, font-lock will call us to actually fontify the changed
;; region. We'll walk the AST and for each leaf node, calculate the
;; appropriate face and apply it.
;;
;; If font-lock doesn't call expand-after-change-region (e.g., because
;; we're explicitly fontifying a buffer on first display or after a
;; scroll), we'll construct the AST when our matcher is called.
;;

(make-variable-buffer-local
 (defvar jez-current-grammar nil
   "The grammar in use for the current buffer."))

(make-variable-buffer-local
 (defvar jez-current-parser nil
   "The parser for the current buffer."))

(make-variable-buffer-local
 (defvar jez-current-state nil
   "The state for the current buffer."))

(make-variable-buffer-local
 (defvar jez-current-pos nil
   "The point for the state in the current buffer."))

(make-variable-buffer-local
 (defvar jez-ast nil
   "The current AST for this buffer, or nil if not valid."
   )  )

(defun jez-before-change (beg end)
  "Run before a change to invalidate cached state."
  (setf jez-ast nil))

(defun jez-extend-after-change-region (beg end old-len)
  ;; XXX: avoid big dumb refontification
  (cons (point-min) (point-max)))

(defun jez-font-lock-matcher (limit)
  "Font-lock matcher that applies highlights for a jezebel AST."

  ;; Get the jezebel AST for this buffer
  
  
  ;; Tell font-lock not to try to apply any highlights
  nil)

(defun jez-setup-buffer (grammar)
  "Call as part of mode initialization."
  (setf jez-current-grammar grammar)
  (setf jez-current-parser (jez-compile grammar))
  (setf font-lock-extend-after-change-region-function
        #'jez-extend-after-change-regione)
  (add-hook 'before-change-functions #'jez-before-change nil t))

(provide 'jezebel-mode)
