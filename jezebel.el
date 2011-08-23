(require 'cl)
(require 'jezebel-util)

;; (declare (optimize (speed 3) (safety 0)))

(defstruct (jez-parser
            (:constructor jez--make-parser)
            (:copier nil)
            (:conc-name jez-parser--))
  
  "A compiled parser that can be used to transform a series of 
tokens into an AST."

  ;; Rules extracted from the grammar description with which this
  ;; parser was created.
  (rules (make-hash-table))

  ;; Primitives extracted from the grammar description with which this
  ;; parser was created.
  (primitives (make-hash-table))

  ;; Holds initial state symbol for this parser.
  (initial-state nil)

  ;; Maps rule invocations to their resulting state symbols. Every
  ;; value in this hash is also a value in states.
  (expansion-cache (make-hash-table :test 'equal))

  ;; Maps IR forms (jez--do-* args...) to state symbols.
  (states (make-hash-table :test 'equal)))

(defun* jez--make-pstate (parser function &rest args)
  (symbol-macrolet ((states (jez-parser--states parser)))
    (let ((ir `(,function ,@args)))
      (or
       (gethash ir states)
       (let ((state-sym (gensym (format "jez-state-%s" function))))
         (put state-sym 'ir ir)
         (puthash ir state-sym states))))))

(defstruct (jez-state
            (:constructor jez--make-state)
            (:copier nil)
            (:conc-name jez-state--))
  
  "The state of an ongoing parse."

  ;; The parse tree we've constructed so far, a jez-tree instance
  ast

  ;; Reach (buffer position)
  (reach 0)

  ;; Stack states to enter when backtracking
  (or-stack (make-vector 1024 nil))
  (or-stack-pos 0)

  ;; Stack of states to enter when successful
  and-stack

  ;; Reference to the parser that created us (which is immutable)
  parser)

(define-functional-struct (jez-environment
                           (:constructor jez--make-environment)
                           (:conc-name jez-environment--))

  "A lexical environment used during rule compilation.  Pure
functional data structure."

  ;; The parser for this environment
  parser)

(defun* jez--normalize-rd (rd)
  (etypecase rd
    (symbol     (jez--normalize-rd (list rd)))
    (character  (jez--normalize-rd (char-to-string rd)))
    (string     (jez--normalize-rd (list 'literal rd)))
    (list       rd)))

(defun* jez-expand-rd-1 (env rd)
  "Expand a rule RD once in ENV.  Return a list (EXPANDED NEW-RD)
where EXPANDED is true if we we were able to expand the rule, and
NEW-RD is the expanded definition, or the original definition if
we were uanble to expand."

  (let* ((norm-rd (jez--normalize-rd rd))
         (ruledef (gethash (car-safe norm-rd)
                           (jez-parser--rules
                            (jez-environment--parser env)))))
    (if ruledef
        (list t (apply ruledef (rest norm-rd)))
      (list (not (eq rd norm-rd)) norm-rd))))

(defun* jez-compile-rd (env rd)
  "Return the state symbol for rule-definition RD.
Compile the rule if necessary."

  ;; First, look for RD in the state cache.  If it's already there,
  ;; return the state symbol.  Otherwise, try expanding the rule, and
  ;; if that works, recursively invoke jez-compile-rd on the
  ;; expansion.
  
  ;; Otherwise, if the rule wasn't expanded, we're either at a
  ;; primitive or an invalid rule.  If we're at an invalid rule,
  ;; signal an error.  Otherwise, call the corresponding primitive
  ;; handler to allocate a symbol for the new state and set its `ir'
  ;; property, then return the state.
  
  (let* ((parser (jez-environment--parser env))
         (expansion-cache (jez-parser--expansion-cache parser)))

    (or
     ;; If we've already compiled this rule, return its state symbol.
     (gethash rd expansion-cache)

     ;; Check whether this rule definition can be expanded to a more
     ;; fundamental rule definition. If so, use the state symbol for
     ;; that expansion.
     (destructuring-bind (expanded-p expanded-rd) (jez-expand-rd-1 env rd)
       (when expanded-p
         (jez-compile-rd env expanded-rd)))

     ;; We weren't able to expand the rule further. It is either a
     ;; primitive or not really a rule.
     (or (apply (or (gethash (car-safe rd)
                             (jez-parser--primitives parser))
                    (error "invalid rule %S (no primitive for %S)"
                           rd (car-safe rd)))
                env (rest rd))
         (error "primitive handler unexpectedly returned nil: %S"
                (gethash (car-safe rd)
                             (jez-parser--primitives parser)))))))

(defun* jez--double-vector (vec &optional init)
  "Return a copy of vector VEC of twice its length.  The additional
elements are set to INIT."
  (loop
   with new-vec = (make-vector (* (length vec) 2) init)
   for i from 0 to (length vec)
   do (setf (aref new-vec i) (aref vec i))
   finally return new-vec))

(defmacro jez--push-vector (vec-place pos-place item)
  "Add ITEM to the extensible vector given by VEC-PLACE and
POS-PLACE, expanding the vector if appropriate.

N.B VEC-PLACE and POS-PLACE may be evaluated more than once.
"
  `(progn
     (when (<= (length ,vec-place) ,pos-place)
       (assert (= (length ,vec-place) ,pos-place))
       (setf ,vec-place (jez--double-vector ,vec-place)))
     (setf (aref ,vec-place
                 (prog1 ,pos-place (incf ,pos-place)))
           ,item)))

(defmacro jez--pop-vector (vec-place pos-place)
  "Return and remove the value at the end of the extensible
vector given by VEC-PLACE and POS-PLACE."
  `(prog1
     (aref ,vec-place (decf ,pos-place))
     (assert (>= ,pos-place 0))))

(defun* jez-state-reach-forward (state new-reach)
  (symbol-macrolet ((reach (jez-state--reach state)))
    (assert (>= reach (point-min)))
    (assert (>= new-reach (point-min)))
    (setf reach (max reach new-reach))))

(defun* jez-state-backtrack (state)
  "Back up to most recent choice point in STATE."
  (symbol-macrolet ((os (jez-state--or-stack state))
                    (osp (jez-state--or-stack-pos state)))
    (assert (> osp 0))
    (while (not (funcall (aref os (decf osp)) state)))))

(defun* jez-state-add-undo-1 (state item)
  "Add an undo record to STATE.  

To backtrack, we pop the first item from STATE's or-stack and
call it as a function.  If this function returns nil, we repeat
the process.  The called function may pop additional values from
the or-stack."
  (jez--push-vector (jez-state--or-stack state)
                    (jez-state--or-stack-pos state)
                    item))

(defun* jez-state-add-undo (state &rest items)
  "Add ITEMS to STATE's undo stack.  The last item will be at the
top of the stack."
  (dolist (item items)
    (jez-state-add-undo-1 state item)))

(define-compiler-macro jez-state-add-undo (state &rest items)
  `(symbol-macrolet ((os (jez-state--or-stack state))
                     (osp (jez-state--or-stack-pos state)))
     (when (<= (+ osp ,(length items)) (length os))
       (setf os (jez--double-vector os)))
     ,@(loop for item in items
             collect `(aset os (incf osp) ,item))))
(put 'jez-state-add-undo 'lisp-indent-function 1)

(defun* jez-state-pop-undo (state)
  (jez--pop-vector (jez-state--or-stack state)
                   (jez-state--or-stack-pos state)))

(defun* jez--undo-handle-choice-point (state)
  (goto-char (jez-state-pop-undo state))
  (setf (jez-state--and-stack state) (jez-state-pop-undo state))
  t)

(defun* jez-state-add-choice-point (state state-sym)
  "Add a choice point to STATE."
  
  (jez-state-add-undo state
    (if state-sym
        (cons state-sym (jez-state--and-stack state))
        (jez-state--and-stack state))
    (point)
    #'jez--undo-handle-choice-point))

(defun* jez-state-do-next (state state-sym)
  "Add STATE-SYM to STATE and-stack."
  (push state-sym (jez-state--and-stack state)))

(defun* jez-state-finish-current (state)
  (pop (jez-state--and-stack state)))

(defun* jez--do-sequence (state child-state next-state)
  "Parse-func implementing sequence operations."
  (jez-state-finish-current state)
  (jez-state-do-next state child-state)
  (jez-state-do-next state next-state))

(defun* jez--preprocess-sequence (env terms)
  "Return a list of (TERM . BINDING) pairs for the given terms.
Values are returned in reversed order."
  (reverse
   (loop for term in terms
         collect (if (eq (car-safe term) '<-)
                     (error "XXX implement <-")
                   (cons term nil)))))

(defun* jez--primitive-sequence (env &rest terms)
  "Compile a sequence of terms.  Return the state-sym used to
begin matching the terms."

  ;; This function generates a function that can be pushed onto one of
  ;; our state stacks as the i=0 state.  The generated function
  ;; references other states functions that we compile for this
  ;; sequence.
  ;; Consider (: A_0 A_1 ... A_N ). We have N + 1 states, denoted by
  ;; an integer i ranging over [0, N].  Either:
  ;;
  ;;   - we're about to parse A_i, 0 <= i < N
  ;;   - we've finished parsing, i = N
  ;;
  ;; When we're in state i and need to match A_i next, we need to pass
  ;; into the code for matching A_i enough information for that code
  ;; to then try parsing A_(i+1), possibly many times if backtracking
  ;; is allowed.
  ;;
  ;; We communicate this information by pushing an item onto
  ;; success-stack.
  ;;
  ;; We also allow users to bind values of sub-rules to names using
  ;; the <- operator. These names need to be available during matching
  ;; of sub-rules in order to support predicates --- i.e., each bound
  ;; sub-rule's value needs to be available just after it's matched,
  ;; and not just at the end of the overall rule.
  ;;
  
  ;; Loop forward through all terms, accumulating information about
  ;; which ones bind variables. We don't compile the terms right
  ;; away because each one needs to know its successor.
  
  ;; Having built up intermediate information about the meaning of
  ;; each term, compile the terms in reverse order.

  (loop
   with parser = (jez-environment--parser env)
   for (term . binding) in (jez--preprocess-sequence env terms)
   for state-sym = (jez--make-pstate
                    parser
                    `(match ,(jez-compile-rd env term) ,state-sym))
   finally return state-sym))

(defun* jez--do-repetition (state child-state)
  ;; We don't remove ourselves from the and-stack --- we just match
  ;; the child state over and over until we eventually fail, at which
  ;; point we backtrack and we're done.
  (jez-state-add-choice-point state nil)
  (jez-state-do-next state child-state))

(defun* jez--primitive-repeat (env &rest terms)
  (jez--make-pstate
   parser
   `(repeat ,(jez-compile-rd env (list* ': terms)))))

(defun* jez--do-choice (state child-state next-alternative-state)
  (jez-state-finish-current state)
  (when next-alternative-state
    (jez-state-add-choice-point state next-alternative-state))
  (jez-state-do-next state child-state))

(defun* jez--primitive-ordered-choice (env terms)
  "Compile prioritized choice primitive."

  ;; Just as for sequence, compile terms in reverse order so each can
  ;; refer to the next.  The difference is that we put terms on the
  ;; backtracking stack so that we only try to match the (N+1)th term
  ;; if the Nth term fails.

  (let ((parser (jez-environment--parser env))
        state-sym)
    
    (dolist (term (reverse terms))
      (setf state-sym
            (jez--make-pstate
             parser
             `(choose ,(jez-compile-rd env term) ,state-sym))))

    ;; The state compiled last is logically first.  Return it.
    state-sym))

(defun* jez--do-literal (state str)
  (jez-state-finish-current state)
  (let ((qstr (concat "\\'" (regexp-quote str))))
    (jez-state-reach-forward state (length str))
    (unless (re-search-forward qstr nil t)
      (jez-state-backtrack state))))

(put 'match-string 'jez-state-function #'jez--do-literal)

(defun* jez--primitive-literal (env &rest terms)
  (jez--make-pstate
   (jez-environment--parser env)
   `(match-string ,(mapconcat #'identity terms ""))))

(defun* jez--grammar-:include (parser other-grammar)
  (jez--slurp-grammar parser other-grammar))

(defun* jez--grammar-:macro (parser macro-name args &rest body)
  (check-type macro-name symbol)
  (check-type args list)
  (puthash macro-name
           `(lambda ,args ,@body)
           (jez-parser--rules parser)))

(defun* jez--grammar-:primitive (parser primitive-name handler)
  (check-type primitive-name symbol)
  (puthash primitive-name handler (jez-parser--primitives parser)))

(defun* jez--slurp-grammar (parser grammar)
  "Update the rules in PARSER from GRAMMAR.  This function must
be called only during initial parser creation."
  
  (when (symbolp grammar)
    (setf grammar (symbol-value grammar)))
  
  (dolist (clause grammar)
    ;; Every grammar clause must begin with a symbol.
    (unless (and (car-safe clause) (symbolp (car clause)))
      (error "invalid grammar clause %S" clause))
      
    ;; (X ...) is equivalent to (:rule X ...) if X is a non-keyword
    ;; symbol. This formulation alows users to express simple rules
    ;; simply.
    (unless (keywordp (car clause))
      (push :rule clause))

    ;; (:rule NAME ...) -> (:macro NAME () '(: ...)).
    (when (eq (car clause) :rule)
      (setf clause `(:macro ,(cadr clause) () '(: ,@(cddr clause)))))

    ;; Call the function that processes this clause.
    (apply (or (intern-soft (format "jez--grammar-%s" (car clause)))
               (error "unknown clause type %S" (car clause)))
           parser
           (cdr clause))))

(defun* jez-compile (grammar &optional (top-rd 'top))
  "Compiles GRAMMAR into a jez-parser. Return the new parser instance.
TOP-RD denotes with which the generated parser will begin
parsing; by default, we begin with the rule called `top'."

  ;; Start with an empty parser and empty lexical environment.
  (let* ((parser (jez--make-parser))
         (env (jez--make-environment :parser parser)))
    
    ;; Fill in rules and primitives from GRAMMAR.
    (jez--slurp-grammar parser grammar)

    ;; Compile the rule graph rooted at TOP to the intermediate
    ;; representation.
    (setf (jez-parser--initial-state parser)
          (jez-compile-rd env top-rd))

    ;; Optimize the intermediate representation.
    ;; XXX: implement optimizer

    ;; For each state, create a byte-compiled elisp function to
    ;; transition to the next state.
    (jez-map-reachable-states parser
                              (jez-parser--initial-state parser)
                              #'jez--compile-to-functions)

    ;; Parser is now ready to use.
    parser))

(defun* jez-describe-parser (parser &key force-macro)
  "Return the grammar parsed by PARSER."
  (symbol-macrolet ((rules (jez-parser--rules parser))
                    (primitives (jez-parser--primitives parser)))
    (let ((rule-names
           (loop for x being the hash-keys of rules
                 collect x))
          (primitive-names
           (loop for x being the hash-keys of primitives
                 collect x)))
      (setf rule-names (sort rule-names #'string<))
      (setf primitive-names (sort primitive-names #'string<))
      `(,@(loop for primitive-name in primitive-names
                for primitive = (gethash primitive-name primitives)
                collect `(:primitive ,primitive-name ,primitive))
        ,@(loop with inner
                for rule-name in rule-names
                for (nil args . def) = (gethash rule-name rules)
                ;; If def looks like (lambda () '(: . X)) for some X,
                ;; generate (,rule-name ,X). Otherwise, use the more
                ;; general (:macro ,rule-name ,args ,@def) syntax. The
                ;; former syntax is what :rule produces.
                collect (if (and (not force-macro)
                                 (null args)
                                 (setf inner (car def))
                                 (null (cdr def))
                                 (eq (car-safe inner) 'quote)
                                 (setf inner (cdadr inner))) 
                            `(,rule-name ,@inner)
                          `(:macro ,rule-name ,args ,@def)))
        ))))

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
    (jez-state-add-choice-point state 'jez--pseudostate-fail)

    ;; After we're successfully parsed everything, transition to a
    ;; state that succeeds forever.
    (jez-state-do-next state 'jez--pseudostate-done)

    ;; Begin parsing in the initial state.
    (jez-state-do-next state (jez-parser--initial-state parser))

    ;; Parser is now ready for use.
    state))

(defun* jez-advance (state)
  "Update parse state STATE.  Return the symbol `done' if we are
at the end of input, `fail' if we are at an error state, or nil
otherwise."
  (funcall (first (jez-state--and-stack state))
           state))

(defconst jez-root-grammar
  '(;; Fundamental combinators.
    (:primitive : jez--primitive-sequence)
    (:primitive * jez--primitive-repeat)
    (:primitive / jez--primitive-ordered-choice)
    
    ;; Literal handling (note: the compiler automagically transforms
    ;; an RD X into (literal X) if X is a character or string.
    (:primitive literal jez--primitive-literal)))

(provide 'jezebel)
