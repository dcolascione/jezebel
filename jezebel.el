(require 'cl)
(require 'jezebel-util)
(require 'jezebel-engine)
(require 'jezebel-grammar)

;;; Grammar compiler

(defun* jez--pseudostate-done (state)
  'done)

(defun* jez--psuedostate-fail (state)
  'fail)

(defun* jez-begin-parse (parser)
  "Create a new parse state."
  (let ((state (jez--make-state :parser parser
                                :reach (point-min))))

    ;; If we try to backtrack past a choice point, there is no
    ;; possible way to continue.  Arrange to transition to a state
    ;; that fails forever in this case.
    (jez-add-choice-point state 'jez--pseudostate-fail)

    ;; After we're successfully parsed everything, transition to a
    ;; state that succeeds forever.
    (jez-do-next state 'jez--pseudostate-done)

    ;; Begin parsing in the initial state.
    (jez-do-next state (jez-parser--initial-state parser))

    ;; Parser is now ready for use.
    state))

(defun* jez-advance (state)
  "Update parse state STATE.  Return the symbol `done' if we are
at the end of input, `fail' if we are at an error state, or nil
otherwise."
  (funcall (first (jez-state--and-stack state))
           state))



(provide 'jezebel)
