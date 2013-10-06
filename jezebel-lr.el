;; -*- lexical-binding: t -*-

;;
;; This file contains code that implements a dynamic GLR parser based
;; on Wagner and Graham's "Incremental Analysis of Real Programming
;; Languages" paper.  It consists of two main components:
;;
;; - The grammar compiler
;;
;; - The compiled-grammar driver
;;
;; The grammar compiler generates LR tables from an _arbitrary_ CF
;; grammar using the LALR(1) algorithm.  A key difference between this
;; table generator and the one in popular LALR(1) parser generators is
;; that we don't resolve conflicts statically.  Instead, we rely on
;; the GLR parser driver to resolve conflicts for us.
;;
;; We use the Dragon Book algorithm for computing the LALR lookahead
;; set.  Some algorithms run faster; other algorithms are simple. But
;; this one is widely-known and fast enough.
;;
;; The compiled-grammar uses these LR parsing tables to run a GLR
;; parse over a token stream.  Briefly, GLR parsers deal with
;; shift-reduce and reduce-reduce conflicts by forking the parse state
;; and trying both alternatives.  The result is a parse forest.
;;

(require 'jezebel-util)

(defconst jez-epsilon-sym -1
  "Special symbol number used to indicate an epsilon production")

(defconst jez-end-sym -2
  "Special symbol number used to indicate end of input")

(defstruct jez-lr
  ;; Hash mapping syms (terminals and nonterminals) to allocated
  ;; numbers.
  sym->symno

  ;; All symbol numbers >= this value refer to nonterminals
  min-nonterm

  ;; Array of productions, which is essentially a vectorized form of
  ;; the grammar input.  For each production i, (aref productions i)
  ;; is a cons (NONTERMNO, RHS), where NONTERMNO is the symbol number
  ;; of the production and RHS is a possibly-empty list representing
  ;; the symbols produced.
  productions

  ;; Array mapping (- SYMNO MIN-NONTERM) to list of productions that
  ;; produce SYMNO.  Query with jez-lr-production-rules-for-symbol.
  produces)

(defun jez-lr-number-symbols (lr)
  "Return the total number of symbols in LR."
  (+ (length (jez-lr-produces lr))
     (jez-lr-min-nonterm lr)))

(defun jez-lr-slurp-grammar (rules terminals start)
  "Construct a jez-lr object."

  (unless rules
      (error "no rules supplied"))

  (unless terminals
      (error "no terminals supplied"))

  ;; Because we use our own production to wrap the user's start
  ;; symbol, we're guaranteed to have only one production for the
  ;; whole grammar, even if the user's declared start symbol
  ;; actually has many productions.  This start symbol is also
  ;; guaranteed to be the lowest-numbered non-terminal and to be
  ;; production number 0.

  (push (list 'jez-real-start start) rules)

  (let* ((next-symno 0)
         (min-nonterm nil)
         (produces nil)
         (sym->symno (make-hash-table :test 'eq))
         (productions (make-vector (length rules) nil)))

    ;; Incorporate the user-supplied term->termno mapping into our
    ;; internal mapping, and start assigning symbol numbers only after
    ;; assigning user numbers.

    (dolist (terminals-entry terminals)
      (let ((term (car terminals-entry))
            (termno (cdr terminals-entry)))
        (unless (symbolp term)
          (error "terminal must be symbol: %s" term))
        (unless (integerp termno)
          (error "termno must be integer: %s" termno))
        (when (gethash term sym->symno)
          (error "terminal already defined: %s" term))
        (setf next-symno (max next-symno (1+ termno)))
        (puthash term termno sym->symno)))

    ;; Assign numbers to non-terminals. next-symno is greater than any
    ;; user-supplied terminal and we can carve out internal numbers
    ;; for our terminals.

    (setf min-nonterm next-symno)

    (dolist (production rules)
      (let ((nonterm (first production)) nontermno)
        (unless (symbolp nonterm)
          (error "non-terminal must be symbol: %s" nonterm))

        (setf nontermno (gethash nonterm sym->symno))
        (when (and nontermno
                   (< nontermno min-nonterm))
          (error "cannot produce a terminal: %s" nonterm))

        (unless nontermno
          (setf nontermno next-symno)
          (incf next-symno)
          (puthash nonterm nontermno sym->symno))))

    ;; Now vectorize the parsing rules.

    (setf produces (make-vector (- next-symno min-nonterm) nil))

    (loop for (nonterm . rhs) in rules
          for prodidx upfrom 0
          for nontermno = (gethash nonterm sym->symno)
          for rhslst = (or (loop for sym in rhs
                                  collect (or (gethash sym sym->symno)
                                              (error "unknown symbol: %s" sym)))

                           ;; An empty right side is actually an
                           ;; epsilon production.  It's still a
                           ;; non-terminal, so we want
                           ;; jez-lr-production-rules-for-symbol to
                           ;; return something.

                           (list jez-epsilon-sym))

          do (aset productions prodidx (cons nontermno rhslst))
          and do (push prodidx
                       (aref produces (- nontermno min-nonterm))))

    ;; Return a jez-lr object embodying the parsed, checked grammar.

    (make-jez-lr
     :sym->symno sym->symno
     :min-nonterm min-nonterm
     :productions productions
     :produces produces)))

(defun jez-lr-compute-nullability (lr)
  "Compute the nullability information for LR."
  (loop
   with nsymbols = (jez-lr-number-symbols lr)
   with nullability = (make-bool-vector nsymbols nil)
   with productions = (jez-lr-productions lr)
   while (loop
          with changed = nil
          for (lsymno . rhs) across productions
          for rhs-nullable = (loop for rsymno in rhs
                                   always (or (eq rsymno jez-epsilon-sym)
                                              (aref nullability rsymno)))
          if rhs-nullable
          do (unless (aref nullability lsymno)
               (aset nullability lsymno t)
               (setf changed t))
          finally return changed)
   finally return nullability))

(defun jez-lr-nullable-p (lr symno)
  "Is the given symbol nullable?"
  (aref (jez-lr-nullability lr) symno))

(defun jez-lr-production-rules-for-symbol (lr symno)
  "Find what production rules produce nonterminal SYMNO.
If symno is a terminal or nil, return nil.  Otherwise,
return a list of production numbers.
"
  (let ((min-nonterm (jez-lr-min-nonterm lr)))
    (if (and symno
             (<= min-nonterm symno))
        (aref (jez-lr-produces lr)
              (- symno min-nonterm)))))

;;
;; Int-sets are useful for various parser operations.  As the name
;; might suggest, int-sets hold small, sparse sets of integers,
;; usually representing terminals, parser symbols, productions, and so
;; on.  They support union, intersection, and so on.
;;
;; N.B. all sets with the same contents have the same sxhash and are
;; #'equal.
;;
;; We implement intsets as lists today, but (XXX) abstract them
;; here so we can switch over to hash tables, search trees, or
;; other primitives if we see performance problems here.
;;

(defun jez-make-int-set (&optional initial-contents)
  "Make a new int set object."
  (cons 'jez-int-set
        (and initial-contents
             (delete-consecutive-dups
              (sort
               (copy-sequence initial-contents)
               #'<)))))

(defun jez-int-set-p (is)
  (eq (car-safe is) 'jez-int-set))

(defun jez-copy-int-set (is)
  "Copy int set object IS."
  (check-type is jez-int-set)
  (copy-sequence is))

(defun jez-int-set-add (is int)
  "Add integer INT to int-set object IS.
Return non-nil if we changed IS."
  (check-type is jez-int-set)
  (unless (memq int is)
    (setcdr is (sort (cons int (cdr is)) #'<))))

(defun jez-int-set-remove (is int)
  "Remove an element INT from int-set IS."
  (check-type is jez-int-set)
  (setcdr is (delq int (cdr is))))

(defun jez-int-set-empty-p (is)
  "Is the int-set IS empty?"
  (check-type is jez-int-set)
  (null (cdr is)))

(defun jez-int-set-member-p (is int)
  "Is INT a member of IS?"
  (check-type is jez-int-set)
  (memq int (cdr is)))

(defmacro* jez-do-int-set ((var is) &rest body)
  "Like dolist, but for int-sets."
  `(dolist (,var (cdr ,is))
     ,@body))

(defun jez-int-set-as-list (is)
  "Return the contents of int-set IS as a list"
  (cdr is))

(defun jez-int-set-union (is merge-from)
  "Set IS to union of IS and MERGE-FROM.
Return whether we changed IS.  MERGE-FROM is
unchanged."

  (check-type is jez-int-set)
  (check-type merge-from jez-int-set)
  (pop merge-from)

  (let (changed)
    (while merge-from
      (cond ((or (null (cdr is))
                 (< (car merge-from) (cadr is)))
             (setcdr is (cons (car merge-from) (cdr is)))
             (setf changed t)
             (pop merge-from)
             (pop is))
            ((= (car merge-from) (cadr is))
             (pop merge-from)
             (pop is))
            (t
             (assert (> (car merge-from) (cadr is)))
             (pop is))))
    changed))

(defconst jez-empty-int-set (jez-make-int-set))

(put 'jez-do-int-set 'lisp-indent-function 1)

(defun jez-lr0-item-< (a b)
  "Compare two LR(0) items."
  (cond ((< (car a) (car b)) t)
        ((> (car a) (car b)) nil)
        ((< (cdr a) (cdr b)) t)))

(defun jez-lr0-closure (lr items)
  "Close over the given LR(0) items.
Each item is a cons (PRODNO . DOTPOS).  Return a new list of
items."

  (let ((productions (jez-lr-productions lr))
        (to-process items)
        (item-to-close nil)
        (next-productions nil)
        (closed-items (copy-sequence items))
        (next-item nil))

    (while to-process
      (setf item-to-close (pop to-process))

      ;; The production (entry in the productions array) is a cons
      ;; (LHS . RHS), where LHS is the non-terminal being produced and
      ;; RHS is a list of symbols that LHS generates. Here, we
      ;; determine the item to the right of the dot in one step.  If
      ;; the dot is at the end of the production, NTH below returns
      ;; nil.

      ;; next-productions is a list of production numbers that can
      ;; produce next-symno.  Because next-productions is nil if nth
      ;; returned nil (dot at end) or a terminal, we only add
      ;; nonterminals in the loop below.

      (setf next-productions
            (jez-lr-production-rules-for-symbol
             lr
             (nth (1+ (cdr item-to-close))
                            (aref productions (car item-to-close)))))

      (while next-productions
        (setf next-item (cons (pop next-productions) 0))
        (unless (member next-item closed-items)
          (push next-item closed-items)
          (push next-item to-process))))

    (sort closed-items #'jez-lr0-item-<)))

(defun jez-lr0-goto (lr items symno)
  "Compute the goto function on a set of LR(0) items.
Each item is a cons (PRODNO . DOTPOS).  This routine returns a
closed set of LR(0) items."

  (let ((productions (jez-lr-productions lr))
        (item nil)
        (goto-set nil))

    (while items
      (setf item (pop items))
      (when (eq symno (nth (1+ (cdr item)) (aref productions (car item))))
        (push (cons (car item) (1+ (cdr item))) goto-set)))

    (jez-lr0-closure lr goto-set)))

(defun jez-lr0-kernel (items)
  "Compute the kernel (dotpos nonzero) for an LR(0) state."

  (loop for item in items
        for (prodno . dotpos) = item
        if (or (= prodno 0) (> dotpos 0))
        collect item))

(defun jez-make-tx (from via to)
  "Make a new transition.
FROM is the state number being transitioned from.  VIA is the
symbol number on which the transition is happening.  TO is the
destination state number."
  (list* from via to))

(defun jez-tx-from (transition)
  (car transition))

(defun jez-tx-via (transition)
  (cadr transition))

(defun jez-tx-to (transition)
  (cddr transition))

(defun jez-compute-lr0-states (lr)
  "Compute the LR(0) DFA for grammar LR.
Return (STATES . TRANSITIONS).

STATES is an ordered vector of states, where each state is an
ordered list of LR(0) items, each item being of the form (PRODNO
. DOTPOS).  The ordering is by jez-lr0-item-<.  The ordering of
items within each state has no significance except to ensure that
equal states are EQUAL.

TRANSITIONS is a jez-txdb object that describes the transitions.

"

  (let ((stateno 0)
        (statehash (make-hash-table :test 'equal))
        (nsymbols (jez-lr-number-symbols lr))
        (to-process nil)
        (current-state nil)
        (current-stateno nil)
        (next-state nil)
        (next-stateno nil)
        (state-list nil)
        (transitions nil))

    ;; Each entry on the to-process list is a cons of (STATENO
    ;; . STATE).  statehash maps states (which are EQUAL-equal if they
    ;; are logically equal) to their state numbers so that we can
    ;; quickly find the number of a state we've already added.

    ;; N.B. Because the initial production of our grammar is always
    ;; production number zero, and the dot is always at the left end
    ;; of this production in the initial state, we can hardcode '(0 0)
    ;; below.

    (setf current-state (jez-lr0-closure lr '((0 . 0))))
    (push (cons 0 current-state) to-process)
    (push current-state state-list)
    (puthash current-state 0 statehash)

    (while to-process
      (setf current-state (pop to-process))
      (setf current-stateno (pop current-state))

      ;; For each symbol symno in our grammar, see whether any item in
      ;; current-state is about to generate that symbol, and if so,
      ;; build a new state for the transition.

      (dotimes (symno nsymbols)
        (setf next-state (jez-lr0-goto lr current-state symno))
        (when next-state ; Skip impossible transitions
          (setf next-stateno (gethash next-state statehash))

          ;; If we've already generated the destination state, just
          ;; add a transition from the current state to the next
          ;; state.  We don't need to process the new state again.  We
          ;; process each state exactly once, so we're guaranteed not
          ;; to add duplicates to the transitions list.  If the state
          ;; is new to us, then of course we need to process the new
          ;; state.

          (unless next-stateno
            (setf next-stateno (incf stateno))
            (push next-state state-list)
            (push (cons next-stateno next-state) to-process)
            (puthash next-state next-stateno statehash))

          (push (jez-make-tx current-stateno symno next-stateno)
                transitions))))

    ;; Done.  Reverse the state list because we accumulated it by
    ;; consing onto the front instead of appending to the end.

    (list (apply #'vector (nreverse state-list))
          (jez-make-txdb
           (nreverse transitions)
           (jez-lr-min-nonterm lr)))))

(defstruct (jez-txdb
            (:constructor jez--make-txdb)
            (:copier nil)
            (:conc-name jez-txdb--))
  transitions
  ntt
  min-nonterm)

(defun jez-make-txdb (transition-list min-nonterm)
  "Make an object that can be used to query transitions.

TRANSITION-LIST is a list of transition objects.  MIN-NONTERM is
the smallest non-terminal symbol number.

Note that the returned structure references TRANSITION-LIST by
reference.  Either guarantee its immutability or supply a copy. "

  (jez--make-txdb
   :transitions transition-list
   :ntt (apply #'vector
               (loop for transition in transition-list
                     for via = (jez-tx-via transition)
                     when (>= via min-nonterm)
                     collect transition))
   :min-nonterm min-nonterm))



(defun* jez-txdb-query (txdb
                        &key
                        from
                        via
                        to
                        kind
                        (want 'tx)
                        test
                        just-one)
  "Retrieve transitions database matching given criteria.

TXDB is a transitions database object created by `jez-make-txdb'.

FROM, VIA, TO, and KIND are filters.  If a filter parameter is
supplied and non-nil, any returned transition must match the
supplied parameer.  FROM and TO are state numbers.  VIA is a
symbol number.

KIND imposes an additional requirement on VIA and is either
'terminal or 'non-terminal.

WANT controls the type of returned value: if it is 'tx, return
transition objects.  If WANT is 'txn, return nonterminal
transition numbers.  If WANT is any other value, it is a funciton
to call on transition objects before extracting the result.  For
example, you can find all the terminal symbols that transition away
from state S by calling

    (jez-txdb-query txdb
      :from S
      :kind 'terminal
      :want #'jez-tx-via)

This approach is more efficient than retrieving the transaction
objects, calling jez-tx-via on them yourself, and building up a
list of results.  This manual approach requires consing up a list
that we just throw away.  By using :want, we can avoid this
unnecessary allocation.

If WANT is 'txn, then KIND must be 'non-terminal.  WANT defaults
to 'tx.

If TEST is non-nil, it is a function called with one argument,
the transition object.  That transition object is added to the
result set only if TEST returns non-nil.

If JUST-ONE is t, instead of returning a list of matching
terminals or terminal numbers, return the single matching
terminal number.

"
  (check-type from (or integer null))
  (check-type via (or integer null))
  (check-type to (or integer null))
  (check-type kind (member terminal non-terminal nil))
  (check-type want (or (member tx txn) function))
  (check-type just-one boolean)
  (check-type test (or function null))

  (when (eq want 'txn)                  ; Skip test if implicit
    (assert (eq kind 'non-terminal) nil
            "Only non-terminal transitions are numbered"))

  (let* ((min-nonterm (jez-txdb--min-nonterm txdb)))
    (cl-macrolet
        ((TXTEST
          ()
          `(and (or (not from)
                    (eq from (jez-tx-from tx)))
                (or (not via)
                    (eq via (jez-tx-via tx)))
                (or (not to)
                    (eq to (jez-tx-to tx)))
                (cond ((eq want 'txn) t)
                      ((eq kind 'terminal)
                       (< (jez-tx-via tx) min-nonterm))
                      ((eq kind 'non-terminal)
                       (>= (jez-tx-via tx) min-nonterm))
                      (t t))
                (or (not test)
                    (funcall test tx)))))
      (cond ((eq want 'txn)
             (loop with ntt = (jez-txdb--ntt txdb)
                   for txn below (length ntt)
                   for tx = (aref ntt txn)
                   for match = (TXTEST)
                   if (and match just-one)
                   return txn
                   if match
                   collect txn))
            ((eq want 'tx)
             (loop for tx in (jez-txdb--transitions txdb)
                   for match = (TXTEST)
                   if (and match just-one)
                   return tx
                   if match
                   collect tx))
            (t
             (loop for tx in (jez-txdb--transitions txdb)
                   for match = (TXTEST)
                   if (and match just-one)
                   return (funcall want tx)
                   if match
                   collect (funcall want tx)))))))

(put 'jez-txdb-query 'lisp-indent-function 1)

(defun jez-txdb-txn->tx (txdb txn)
  "Return the jez-tx object for a nonterminal transition number."
  (aref (jez-txdb--ntt ,txdb) ,txn))

(defun jez-txdb-number-txns (txdb)
  "Return the number of nonterminal transitions."
  (length (jez-txdb--ntt txdb)))

(defun jez-digraph (R FP nr-X)
  "DeRemer and Pennello \"Digraph\" function to compute closure.

We deem X = { x | 0 <= x < nr-X }.

R is a Lisp function describing a relation: given an x, return a
list of all y such that the relation xRy holds.

FP is a Lisp function mapping from elements of X to int-sets.

Return F, a Lisp vector describing a function from elements of X
to the int-sets FP returned, propagated across all relationships
R.

"

  (loop with S = (cons nil 0) ; car: stack; cdr: stack size
        with N = (make-vector nr-X 0)
        with F = (make-vector nr-X nil)
        for x below nr-X
        when (eq (aref N x) 0)
        do (jez-traverse x N S F nr-X R FP)
        finally return F))

(defun jez-traverse-stack-pop (S)
  (decf (cdr S))
  (pop (car S)))

(defun jez-traverse-lazy-fetch (FP F x)
  (or (aref F x)
      (setf (aref F x) (funcall FP x))))

(defun jez-traverse (x N S F nr-X R FP)
  "Helper function for jez-digraph."

  (let (d)
    (push x (car S))
    (setf d (incf (cdr S)))
    (setf (aref N x) d)

    (dolist (y (funcall R x))
      (when (eq (aref N y) 0)
        (jez-traverse y N S F nr-X R FP))

      (setf (aref N x) (min (aref N x) (aref N y)))

      ;; (F x) <- (F x) U (F y)
      (jez-int-set-union
       (jez-traverse-lazy-fetch FP F x)
       (jez-traverse-lazy-fetch FP F y)))

    (when (eq (aref N x) d)
      (let ((top (caar S)))
        (setf (aref N top) most-positive-fixnum)
        (jez-traverse-lazy-update F top x)
        (let ((e (jez-traverse-stack-pop S)))
          (while (not (eq e x))
            (setf top (caar S))
            (setf (aref N top) most-positive-fixnum)

            (unless (eq top x)
              ;; F(Top of S) <- (F x)
              (setf (aref F top)
                    (jez-copy-int-set
                     (jez-traverse-lazy-fetch FP F x))))

            (setf e (jez-traverse-stack-pop S))))))))

(defun jez-reversed-rhs (lr prodno)
  "Return the reversed RHS for a given production in LR."
  (reverse (cdr (aref (jez-lr-productions lr) prodno))))

(defun jez-lhs (lr prodno)
  "Return the non-terminal symno produced by prodno."
  (car (aref (jez-lr-productions lr) prodno)))

(defun jez-lr-LOOKBACK-impl (P q lr state->tx* state->ntt ntt)
  "Implement LOOKBACK.

P is a production number. Q is a target state number.  LR is a
jez-lr object.  state->tx* indexes transition objects by target
state number.  state->ntt indexes nonterminal transition numbers
by source state number.  ntt maps nonterminal transition numbers
to transition objects.

"

  (let* ((path (jez-reversed-rhs lr P))
         (goal-nontermno (jez-lhs lr P))
         (current-states (list q))
         symno)

    ;; Run the DFA backward to find out from what states we can spell
    ;; path and end up at q.  Note that the DFA run backward is
    ;; actually an NFA, and we're doing direct NFA simulation here.

    (when (eq (car path) jez-epsilon-sym)
      (setf path nil))

    (while path
      (setf symno (pop path))
      (setf current-states
            (loop for sn in current-states
                  nconc
                  (loop for tx-to-sn in (aref state->tx* sn)
                        do (assert (eq (jez-tx-to tx-to-sn) sn))
                        if (eq (jez-tx-via tx-to-sn) symno)
                        collect (jez-tx-from tx-to-sn)))))

    ;; Now we have a set of states p that start our production;
    ;; simulate a "shift" by looking for each p transitions over the
    ;; symbol we're about to reduce in state q.

    (setf current-states
          (delete-consecutive-dups
           (sort current-states #'<)))

    (loop for sn in current-states
          for shift = (loop for ntt-number in (aref state->ntt sn)
                            for tx = (aref ntt ntt-number)
                            for via = (jez-tx-via tx)
                            if (eq via goal-nontermno)
                            return ntt-number)
          do (assert shift) ; Always supposed to succeed
          collect shift)))

(defun jez-lr-READS-impl (txdb nullability tn1)
  "Implement the READS relation."
  (loop for tn2 in (jez-txdb-query txdb
                     :from (jez-tx-to (jez-txdb-txn->tx txdb tn1))
                     :kind 'non-terminal
                     :want 'txn)
        for next-tx = (jez-txdb-txn->tx txdb tn2)
        when (aref nullability (jez-tx-via next-tx))
        collect tn2))

(defun jez-lr-Dr-impl (txdb tn)
  "Provide the Dr set, here represented as a set-valued function.
Return the set of terminals transition away from the state to
which tn transitions."

  (jez-make-int-set
   (append
    (if (eq tn 0) (list jez-end-sym))
    (jez-txdb-query txdb
           :to (jez-tx-to (jez-txdb-txn->tx txdb tn))
           :kind 'terminal
           :want #'jez-tx-via))))

(defun jez-make-lalr-parser (lr)
  "Compute LALR(1) information for LR.
Return not a parse table, but (STATES TRANSITIONS LOOKAHEADS).

STATES is a vector of LR(0) states, each of which is a list of
LR0-item conses.  TRANSITIONS is XXX.  Lookaheads.

"
  ;; We implement the famous DeRemer and Pennello algorithm for
  ;; near-optimal LALR(1) lookahead set construction.

  ;; N.B. Somewhat confusingly, the "relations" in the paper (in bold
  ;; type in the paper, here ALL CAPS) and the sets (capitalized,
  ;; e.g. Read) are both _functions_: the relations are bool-valued
  ;; functions and the capitalized words are set-valued functions.

  (let* ( ;; Vector mapping symno -> nullability bool
         (nullability (jez-lr-compute-nullability lr))

         ;; Raw LR(0) information
         (lr0info (jez-compute-lr0-states lr))
         (states (nth 0 lr0info))
         (txdb (nth 1 lr0info))

         ;; Dr (Direct Reads) set-valued function.  Function maps
         ;; nonterminal transition numbers to int-sets of terminals
         ;; read from the destination state.
         (Dr (lambda (tn1) (jez-lr-Dr-impl txdb tn1)))

         ;; Implements the READS relation: (funcall READS tn1), tn1
         ;; being a nonterminal transition number, returns a list of
         ;; tn2 nonterminal transition numbers.  If tn1 is (p A r), then
         ;; each tn2 is (r C s) where C is a nullable nonterminal
         ;; symbol number and p, r, and s are valid state numbers.
         (READS (lambda (tn1) (jez-lr-READS-impl txdb nullability tn1)))

         ;; Compute Read set by fancy closure algorithm
         (Read (jez-digraph READS Dr (length ntt)))

         ;; Transitions indexed by _destination_ state.  Array maps
         ;; states to jez-tx objects where the array index is
         ;; the transition's TO field.
         (state->tx*
          (loop with state->tx* = (make-vector (length states) nil)
                for tx in transitions
                for to = (jez-tx-to tx)
                do (push tx (aref state->tx* to))
                finally return state->tx*))

         ;; Implement the LOOKBACK relation: (funcall LOOKBACK q P), q
         ;; being a state and P being a production number reduced in
         ;; that state, A->w, returns transition numbers of all
         ;; transitions (p,A) so that P produces A and a path through
         ;; the DFA between p and q spells w.
         (LOOKBACK
          (lambda (q P)
            (jez-lr-LOOKBACK-impl q P lr state->tx* state->ntt ntt)))

         ;; Implement the INCLUDES relation: (funcall INCLUDES tn1)
         ;; returns all tn2, tn1 and tn2 being nonterminal transition
         ;; numbers, (f1 A t1) and (f2 B t2) respectively being the
         ;; transition components, such that there exists some path
         ;; through the grammar from f1 to f2 (NOT t2!) spelling β,
         ;; and there exists a production of the form B→βAγ, where γ
         ;; is nullable.
         ;;
         ;; To compute these tn2, we consult a pre-computed table
         ;; mapping each non-terminal C to a set of (P . i), where P
         ;; is a production rule and i is the offset in production
         ;; rule at which A appears, such that everything to the right
         ;; of A is nullable.  (Note that a single production can have
         ;; many such sets, since a non-terminal can be both nullable
         ;; and appear in the same production rule more than once!).
         ;;
         ;; INCLUDES first uses this table to build a set of (B P β)
         ;; 3-tuples, where B = C in the above table and β is the
         ;; possibly-empty string of symbols in production P that
         ;; appear before i.  For each tuple, we run the state machine
         ;; backward and
         ;;

         )

    Read

    ))

(defun jez-make-lr-table (grammar)
  "Generate an LR parse table from GRAMMAR.

GRAMMAR is a list of the form (PRODUCTIONS TERMINALS START).  We
expect higher-level code to have produced a grammar of this form
from a user-specified grammar written in something more
`rx'-like.

PRODUCTIONS is a list of the form

  (NONTERM SYM_1 SYM_2... SYM_N)

where each SYM is either a Lisp symbol describing either a
terminal or a Lisp symbol listed in TERMINALS.  Empty productions
are allowed, as are unrestricted left and right recursion.

TERMINALS is a list in which each element is of the form

  (TERM . TERMNO)

where each TERM is a Lisp symbol and terminal symbol in GRAMMAR,
and TERMNO is a Lisp integer that the lexer will eventually
supply to the grammar parser in order to drive it forward.  For
maximum efficiency, the maximum TERMNO should be as small as
possible: we build arrays indexed by TERMNO.

"

  (let (lr start rules terminals)

    ;; Vectorize the terminals and production rules.

    (setf rules (first grammar))
    (setf terminals (second grammar))
    (setf lr (jez-lr-slurp-grammar rules terminals start))

    ;; Construct the LR(0) kernels.



    )

  )

(provide 'jezebel-lr)
