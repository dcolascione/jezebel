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
;; The compiled-grammar uses these LR parsing tables to run a GLR
;; parse over a token stream.  Briefly, GLR parsers deal with
;; shift-reduce and reduce-reduce conflicts by forking the parse state
;; and trying both alternatives.  The result is a parse forest.
;;

(require 'jezebel-util)
(require 'cl-lib)
(eval-when-compile '(require 'cl))

(autoload 'xml-escape-string "xml")

(cl-defstruct jez-lr
  ;; Hash mapping syms (terminals and nonterminals) to allocated
  ;; numbers.
  sym->symno

  ;; All symbol numbers >= this value refer to nonterminals
  min-nonterm

  ;; Array of productions, which is essentially a vectorized form of
  ;; the grammar input.  For each production i, (aref productions i)
  ;; is a cons (NONTERMNO . RHS), where NONTERMNO is the symbol number
  ;; of the production and RHS is a possibly-empty list representing
  ;; the symbols produced, each one a symbol number.
  productions

  ;; Array mapping (- SYMNO MIN-NONTERM) to list of productions that
  ;; produce SYMNO.  Query with jez-lr-production-rules-for-symbol.
  produces)

(defun jez-lr-number-symbols (lr)
  "Return the total number of symbols in LR."
  (+ (length (jez-lr-produces lr))
     (jez-lr-min-nonterm lr)))

(defun jez-lr-symbol-name (lr symno)
  "Return the name of the given symbol number."
  (or
   (and (= symno (jez-lr-end-sym lr)) "$")
   (catch 'found
     (maphash (lambda (this-sym this-symno)
                (when (eq this-symno symno)
                  (throw 'found (symbol-name this-sym))))
              (jez-lr-sym->symno lr)))
   (error "no name found for symbol %d" symno)))

(defun jez-lr-end-sym (lr)
  "Return the number of the special end symbol, a terminal."
  (1- (jez-lr-min-nonterm lr)))

(defun jez-lr-number-terminals (lr)
  "Return the number of terminals in LR."
  (jez-lr-min-nonterm lr))

;;
;; jez-lr-item pseudo-object.  Item objects
;; should be considered immutable.
;;

(defun jez-lr-item-prodno (item)
  "Return production rule number of ITEM."
  (car item))

(defun jez-lr-item-dotpos (item)
  "Return dot position of ITEM."
  (cdr item))

(defun jez-lr-make-item (prodno dotpos)
  (cl-check-type prodno integer)
  (cl-check-type dotpos integer)
  (cons prodno dotpos))

(defun jez-lr-slurp-grammar (rules terminals start)
  "Construct a jez-lr object.
RULES is a list of productions.  Each production is a cons of the
form (LHS . RHS), where LHS produces RHS.  LHS is a non-terminal
symbol; RHS is a list of terminal and non-terminal symbols.
TERMINALS is a list of terminals.  Each is a cons cell (TERM
. TERMNO), where TERM is a symbol naming the terminal and TERMNO
is a number associated with that terminal. "

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
  (push (list '^ start) rules)

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

    ;; We reserve the last terminal symbol to represent the end of the
    ;; input.
    (incf next-symno)

    ;; Assign numbers to non-terminals. next-symno is greater than any
    ;; user-supplied terminal and we can carve out internal numbers
    ;; for our terminals.
    (setf min-nonterm next-symno)

    (dolist (production rules)
      (let ((nonterm (first production)) nontermno)
        (unless (symbolp nonterm)
          (error "non-terminal must be symbol: %s" nonterm))
        (setf nontermno (gethash nonterm sym->symno))
        (when (and nontermno (< nontermno min-nonterm))
          (error "terminal cannot be on left side of production: %s"
                 nonterm))
        (unless nontermno
          (setf nontermno next-symno)
          (incf next-symno)
          (puthash nonterm nontermno sym->symno))))

    ;; Now vectorize the parsing rules.
    (setf produces (make-vector (- next-symno min-nonterm) nil))
    (cl-loop
       for (nonterm . rhs) in rules
       for prodidx upfrom 0
       ;; Translate rule into pure numerical form
       for nontermno = (gethash nonterm sym->symno)
       for rhslst = (cl-loop
                       for sym in rhs
                       collect (or (gethash sym sym->symno)
                                   (error "unknown symbol: %s" sym)))
       do (aset productions prodidx (cons nontermno rhslst))
       ;; Separately, maintain a database storing which productions
       ;; can produce a given non-terminal.
       and do (push prodidx
                    (aref produces (- nontermno min-nonterm))))

    ;; Return a jez-lr object embodying the parsed, checked grammar.
    (make-jez-lr
     :sym->symno sym->symno
     :min-nonterm min-nonterm
     :productions productions
     :produces produces)))

(defun jez-lr-compute-nullability (lr)
  "Compute the nullability information for LR.
LR is an LR object. Return is a bool vector giving the
nullability for each symbol."
  (cl-loop
     with nsymbols = (jez-lr-number-symbols lr)
     with nullability = (make-bool-vector nsymbols nil)
     with productions = (jez-lr-productions lr)
     while (cl-loop
              with changed = nil
              for (lsymno . rhs) across productions
              for rhs-nullable = (cl-loop for rsymno in rhs
                                    always (aref nullability rsymno))
              if rhs-nullable
              do (unless (aref nullability lsymno)
                   (aset nullability lsymno t)
                   (setf changed t))
              finally return changed)
     finally return nullability))

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

(defun jez-lr0-item-< (a b)
  "Compare two LR(0) items."
  (cond ((< (jez-lr-item-prodno a) (jez-lr-item-prodno b)) t)
        ((> (jez-lr-item-prodno a) (jez-lr-item-prodno b)) nil)
        ((< (jez-lr-item-dotpos a) (jez-lr-item-dotpos b)) t)))

(defun jez-lr0-closure (lr items)
  "Close over the given LR(0) items.
ITEMS is a list of item objects.  Return a new list of items."
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
      ;;
      ;; TODO: benchmark use of hash table instead of sorted list.
      ;;
      ;; next-productions is a list of production numbers that can
      ;; produce next-symno.  Because next-productions is nil if nth
      ;; returned nil (dot at end) or a terminal, we only add
      ;; nonterminals in the loop below.
      (setf next-productions
            (jez-lr-production-rules-for-symbol
             lr
             (nth (1+ (jez-lr-item-dotpos item-to-close))
                  (aref productions (jez-lr-item-prodno item-to-close)))))
      (while next-productions
        (setf next-item (jez-lr-make-item (pop next-productions) 0))
        (unless (member next-item closed-items)
          (push next-item closed-items)
          (push next-item to-process))))
    (sort closed-items #'jez-lr0-item-<)))

(defun jez-lr0-goto (lr items symno)
  "Compute the goto function on a set of LR(0) items.
Each item is an item object.  This routine returns a closed set
of LR(0) items."
  (let ((productions (jez-lr-productions lr))
        (item nil)
        (goto-set nil))
    (while items
      (setf item (pop items))
      (when (eql symno (nth (jez-lr-item-dotpos item)
                            (cdr (aref productions
                                       (jez-lr-item-prodno item)))))
        (push (jez-lr-make-item (jez-lr-item-prodno item)
                                (1+ (jez-lr-item-dotpos item)))
              goto-set)))
    (jez-lr0-closure lr goto-set)))

(defun jez-lr0-kernel (items)
  "Compute the kernel (dotpos nonzero) for an LR(0) state."
  (cl-loop
     for item in items
     if (or (= (jez-lr-item-prodno item) 0)
            (> (jez-lr-item-dotpos item) 0))
     collect item))

;;
;; Transition pseudo-object.  A transition is a labeled edge between
;; states p--A-->q, pronounced "transition from p to q via A".  If A
;; is a terminal, the transition is a "terminal transition".  If A is
;; a non-terminal, the transition is a "non-terminal transition".
;; Most of the time, we want to talk about non-terminal transitions,
;; so we assign numbers to these transitions.
;;

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
Return a list (STATES TRANSITIONS).

STATES is a vector of states, where each state is an ordered list
of LR(0) items, each item being a jez-lr-item object.  The
ordering of elemets within states is given by jez-lr0-item-<.
The ordering of items within each state has no significance
except to ensure that equal states are EQUAL.

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

      (jez-dbg "current-stateno: %S current-state:%S"
               current-stateno current-state)

      ;; For each symbol symno in our grammar, see whether any item in
      ;; current-state is about to generate that symbol, and if so,
      ;; build a new state for the transition.

      (dotimes (symno nsymbols)
        (setf next-state (jez-lr0-goto lr current-state symno))
        (jez-dbg "symno:%S current-state:%S next-state:%S"
                 symno current-state next-state)
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
           lr))))

(cl-defstruct (jez-txdb
               (:constructor jez--make-txdb)
               (:copier nil)
               (:conc-name jez-txdb--))
  ;; List of all transitions, each one a list (FROM VIA . TO); use the
  ;; jez-tx- accessors.
  transitions
  ;; Vector of transitions; maps non-terminal transition numbers to
  ;; transition objects.
  ntt
  ;; lr object associated with this txdb
  lr)

(defun jez-make-txdb (transition-list lr)
  "Make an object that can be used to query transitions.
TRANSITION-LIST is a list of transition objects.  LR is the LR
object.  Note that the returned structure references
TRANSITION-LIST by reference.  Either guarantee its immutability
or supply a copy. "
  (jez--make-txdb
   :transitions transition-list
   :ntt (apply #'vector
               (cl-loop
                  for transition in transition-list
                  for via = (jez-tx-via transition)
                  when (>= via (jez-lr-min-nonterm lr))
                  collect transition))
   :lr lr))

(defun jez-txdb-nttn->tx (txdb nttn)
  "Find a non-terminal transition by number.
TXDB is a transition database object.  NTTN is a non-terminal
transition number.  Return a jez-tx object."
  (aref (jez-txdb--ntt txdb) nttn))

(defun jez-txdb-tx->nttn (txdb tx)
  "Find a non-terminal transition number."
  (cl-loop
     with ntt = (jez-txdb--ntt txdb)
     for nttn below (length ntt)
     when (eq tx (aref ntt nttn))
     return ntt))

(defun jez-txdb-number-nttns (txdb)
  "Return the number of nonterminal transitions.
TXDB is a transition database object. "
  (length (jez-txdb--ntt txdb)))

(cl-defmacro jez-do-set ((i bv) &rest body)
  "Iterate over the true elements of bool-vector BV.
I is the name of a variable that contains the index of each true
element."
  (let ((bvs (make-symbol "bv")))
    `(let ((,i 0)
           (,bvs ,bv))
       (while
           (progn
             (incf
              ,i (bool-vector-count-consecutive
                  ,bvs
                  nil
                  ,i))
             (< ,i (length ,bvs)))
         (while (progn
                  ,@body
                  (incf ,i)
                  (and (< ,i (length ,bvs))
                       (aref ,bvs ,i))))))))
(put 'jez-do-set 'lisp-indent-function 1)

(defun jez-digraph (R FP nr-X)
  "DeRemer and Pennello \"Digraph\" closure algorithm.

Let X be a set.  Let R be a boolean relationship between elements
of X.  Let F be a set-valued function such that for all x ∈ X

  (F x) = (FP x) ∪ { (F y) | xRy }

F and FP have the same domain (X) and range (Y*).  FP, in a
sense, provides the initial data set of the algorithm.

At the lisp level,

  X = { x | 0 <= x < nr-X }

and FP is a function of one argument, x, x ∈ X.  FP should return
a bool-vector of cardinality Y where the true elements represent
members of the set.

Although R is conceptually a binary, boolean relation, we
implement it in lisp as a set-valued function of domain X and
range X*: given an x ∈ X, return a bool-vector cardinality equal
to X with indexes y, y ∈ X, such that the yth element of the
returned vector is true iff relation xRy holds.

Return a lisp function implementing F.  The lisp function has the
same signature as FP.

See section 4 of Deremer's paper for a detailed explanation of
the algorithm.

Note: at the lisp level, F, FP, and R are all functions of one
argument that return bool vectors, and they all take a single
argument x, x ∈ X.  But while F and FP return subsets of Y, R
returns subsets of X!
"
  (let ((S (cons nil 0)) ; car: stack; cdr: stack size
        (N (make-vector nr-X 0))
        (F (make-vector nr-X nil)))
    (dotimes (x nr-X)
      (when (eq (aref N x) 0)
        (jez-traverse x N S F nr-X R FP)))
    (lambda (x)
         (assert (aref F x))
         (aref F x))))

(defun jez-traverse-stack-pop (S)
  (decf (cdr S))
  (pop (car S)))

(defun jez-traverse (x N S F nr-X R FP)
  "Helper function for jez-digraph."
  ;; N.B. If you are following along with the paper, pay attention to
  ;; the statements in the right margin.  They're not comments, but
  ;; important parts of the algorithm!
  ;;
  ;; XXX: The paper suggests various optimizations to this algorithm.
  ;; We've implemented only the basic version.
  (let (d)
    (push x (car S))
    (setf d (incf (cdr S)))
    (setf (aref N x) d)
    ;; F x <- FP x
    (aset F x (copy-sequence (funcall FP x)))
    (jez-do-set (y (funcall R x))
      (when (eq (aref N y) 0)
        (jez-traverse y N S F nr-X R FP))
      (setf (aref N x) (min (aref N x) (aref N y)))
      (let ((Fx (aref F x))
            (Fy (aref F y)))
        (assert (= (length Fx) (length Fy)))
        ;; (F x) <- (F x) U (F y)
        (bool-vector-union Fx Fy Fx)))
    (when (eq (aref N x) d)
      (while (let ((top (caar S)))
               (setf (aref N top) most-positive-fixnum)
               ;; F(Top of S) <- F x
               (aset F top (copy-sequence (aref F x)))
               (not (eq (jez-traverse-stack-pop S) x)))))))

(defun jez-lr-rhs-for-prodno (lr prodno)
  "Return the right hand side of the given production number"
  (cdr (aref (jez-lr-productions lr) prodno)))

(defun jez-reversed-rhs (lr prodno)
  "Return the reversed RHS for a given production in LR."
  (reverse (jez-lr-rhs-for-prodno lr prodno)))

(defun jez-lr-LOOKBACK-impl (q prod state->tx* state->nttn ntt)
  "Implement LOOKBACK.

LOOKBACK is conceptually a binary, boolean relationship. In Lisp,
we implement the relation as a set-valued function that takes an
LR item as input and returns a set of transition numbers
satisfying the relation.

N.B. Unlike READS and INCLUDES, this relation is _NOT_ between
two non-terminal transitions, but between an LR item and a
transition!

  (q, A→ω) LOOKBACK (p, A) iff p -ω-> q.

PROD is a production (not a production number). Q is a state
number.  STATE->TX* is an array mapping state numbers to lists of
transitions objects that arrive in that state.  STATE->NTTN is an
array mapping state numbers to the numbers of transitions that
depart from that state.  NTT is an array mapping non-terminal
transition numbers possible nonterminal transitions."
  (jez-dbg "LOOKBACK: q:%S prod:%S" q prod)
  ;; Step 1: run the reverse-DFA (which is an NFA) backward from q
  ;; until we find the set of states P, where each p in P satisfies
  ;; the relation above.  At each transition, take an element from ω.
  (let* ((goal-symno (car prod))
         (rhs (cdr prod))
         (cur-states (make-bool-vector (length state->tx*) nil))
         (next-states (make-bool-vector (length state->tx*) nil))
         (i (1- (length rhs))))
    (jez-dbg "goal-symno: %S" goal-symno)
    (jez-dbg "rhs: %S i:%S" rhs i)
    (aset cur-states q t)
    (while (>= i 0)
      (jez-dbg "i: %S" i)
      (fillarray next-states nil)
      (let ((next-sym (nth i rhs)))
        (jez-do-set (cur-state cur-states)
          (jez-dbg "cur-state:%S ltx:%S" cur-state (aref state->tx* cur-state))
          (dolist (leaving-tx (aref state->tx* cur-state))
            (cl-assert (= (jez-tx-to leaving-tx) cur-state))
            (when (= (jez-tx-via leaving-tx) next-sym)
              (aset next-states (jez-tx-from leaving-tx) t)))))
      (cl-psetf cur-states next-states
                      next-states cur-states)
      (decf i))
    ;; Step 2: we have a set of states P that satisfy the relation,
    ;; but don't have the transitions.  Find all transitions from all
    ;; states p in P such that the transition moves us over an A.
    (let ((result (make-bool-vector (length ntt) nil)))
      (jez-do-set (p cur-states)
        (jez-dbg "in final cur-state: %S" p)
        (dolist (nttn (aref state->nttn p))
          (let ((tx (aref ntt nttn)))
            (when (= (jez-tx-via tx) goal-symno)
              (aset result nttn t)))))
      (jez-dbg "LOOKBACK result:%S" (cl-coerce result 'vector))
      result)))

(defun jez-lr-READS-impl (txdb nullability nttn1)
  "Implement the READS relation.
TXDB is a transition database.  NULLABILITY is a bool vector that
maps symbol numbers to true if that symbol is nullable; of
course, only non-terminals are nullable.

READS is conceptually a binary relation, but we implement it as a
set-valued function.  Return a bool vector of cardinality equal
to the number of non-terminal transitions in TXDB where each
index y is a NTTN2 as defined below.  An element NTTN2 in the
returned vector is true if the following relation holds:

  NTTN1 = NTTN of p -A-> r
  NTTN2 = NTTN of r -C->
  (p,A) READS (r,C) iff
    p -A-> r -C->
  and
    NULLABLE(C)"
  (let* ((ntt (jez-txdb--ntt txdb))
         (nr-ntt (length ntt))
         (r (jez-tx-to (aref ntt nttn1)))
         (found (make-bool-vector nr-ntt nil)))
    (dotimes (nttn2 nr-ntt)
      (let ((ntt2 (aref ntt nttn2)))
        (when (and (eq (jez-tx-from ntt2) r)
                   (aref nullability (jez-tx-via ntt2)))
          (aset found nttn2 t))))
    found))

(defun jez-lr-assert-valid-include-table (txdb ictb)
  (let* ((lr (jez-txdb--lr txdb))
         (productions (jez-lr-productions lr)))
    (cl-assert (= (length ictb) (jez-lr-number-symbols lr)))
    (dotimes (symno (length ictb))
      (cl-assert (listp (aref ictb symno)))
      (dolist (ent (aref ictb symno))
        (let* ((prodno (car ent))
               (dotpos (cdr ent))
               (prod (aref productions prodno))
               (rhs (cdr prod)))
          (cl-assert (eq (nth dotpos rhs) symno)))))
    t))

(defun jez-lr-precompute-include-table (txdb nullability)
  "Create a table used for `jez-lr-INCLUDES-impl'.

We create a table mapping every symbol C to a possibly-empty list
of tuples (P . i), where P is a production number and i is a
zero-based index into that production such that the (i-1)th entry
is C and everything in the production from i to the end is
nullable.  This list can contain multiple tuples with the same P
value because a non-terminal can both be nullable and appear in
the same production rule more than once.

For example, if we have production 42: A→C D B E, with E
nullable, then a table entry for B will be (42 . 2).  If we have
another production 43: G→B, then another table entry for B will
be (43 . 0).

TXDB is a transitions database.  NULLABILITY is a bool vector
that maps symbol numbers to whether that symbol is nullable.  The
return value is a vector of length equal to the number of
symbols; the indices are the symbol numbers and the values are
the tuples for each symbol number."
  (let* ((lr (jez-txdb--lr txdb))
         (nsymbols (jez-lr-number-symbols lr))
         (ictb (make-vector nsymbols nil))
         (min-nonterm (jez-lr-min-nonterm lr))
         (productions (jez-lr-productions lr)))
    (dotimes (prodno (length productions))
      (let* ((prod (aref productions prodno))
             (rhs (cdr prod))
             ;; last-nn becomes the 0-based index of last non-nullable
             ;; symbol in RHS; -1 if entire RHS is nullable.
             (last-nn
              (cl-loop
                 with last = -1
                 for i upfrom 0
                 for n in rhs
                 when (not (aref nullability n))
                 do (setf last i)
                 finally return last)))
        ;; Now add a table entry for each nonterminal in RHS that is
        ;; followed by a nullable suffix; we know a symbol at a
        ;; particular index has a nullable suffix because its index is
        ;; >= last-nn.
        (cl-loop
           for i upfrom 0
           for n in rhs
           when (and (>= i last-nn)
                     (>= n min-nonterm))
           do (push (cons prodno i)
                    (aref ictb n)))))
    (cl-assert (jez-lr-assert-valid-include-table txdb ictb))
    ictb))

(defun jez-lr-INCLUDES-impl (txdb ictb state->tx* nttn1)
  "Implement the INCLUDES relation.

TXDB is a transitions database.  INCLUDES is conceptually a
binary relation, but we implement it as a set-valued function.
Return a bool vector of cardinality equal to the number of
non-terminal transitions in TXDB where each index y is a NTTN2 as
defined below.  ICDB is a table as computed by
`jez-lr-precompute-include-table'.  STATE-TX* maps LR0 state
numbers to lists of transition objects (not non-terminal
transition numbers!) that arrive at those state numbers.  An
element NTTN2 in the returned vector is true of the following
relation holds:

  NTTN1 = NTTN of p1 -A->
  NTTN2 = NTTN of p2 -B->

  (p1,A) INCLUDES (p2,B) iff
    B→βAγ
  and
    NULLABLE(γ)
  and
    p2 --β--> p1"

  ;; Using our pre-computed table, we can immediately see which
  ;; productions produce A followed by a nullable suffix.  We then get
  ;; a list of pairs of productions and possibly-empty non-nullable
  ;; prefixes.  We run each prefix backward through the state machine
  ;; from p1; any p2 we successfully reach satisfies the relation.
  ;;
  ;; Note that backward simulation of a DFA can be non-deterministic,
  ;; so we actually simulate an NFA.

  (let* ((ntt (jez-txdb--ntt txdb))
         (nr-ntt (length ntt))
         (found (make-bool-vector nr-ntt nil))
         (A (jez-tx-via (aref ntt nttn1)))
         (lr (jez-txdb--lr txdb))
         (nr-states (length state->tx*))
         (cur-states (make-bool-vector nr-states nil))
         (next-states (make-bool-vector nr-states nil))
         (productions (jez-lr-productions lr)))
    ;; Loop over all B→βAγ, simulating an NFA (which is the reverse of
    ;; the handle-finding LR DFA).
    (dolist (np (aref ictb A))
      ;; Begin with current state equal to p1.
      (fillarray cur-states nil)
      (aset cur-states (jez-tx-from (aref ntt nttn1)) t)
      (let* ((prodno (car np))
             (prod (aref productions prodno))
             (rhs (cdr prod))
             (prefix-length (cdr np))
             (i (1- prefix-length)))
        ;; Walk backward through the state machine, traversing edges
        ;; that correspond to symbols in our current production rule.
        ;; For example, if NTTN1 names transition 60 -A-> 61, and
        ;; we're looking at production A→C D B E for some nullable E,
        ;; i will be 1 (since prefix-length = index of B = 2), and the
        ;; cur-states set will initially contain just 60. The first
        ;; time through the loop, we try to find all states X such
        ;; that X ->D-> 60.  The second time through the loop, we look
        ;; for all states Y such that Y ->C-> x, x ∈ X.  On the third
        ;; iteration, we terminate the loop because i drops below
        ;; zero, indicating that we've run out of prefix symbols.
        ;;
        ;; Alternatively, if prefix-length is 0, i is -1, and nttn1
        ;; itself satisfies the relation (with p1 = p2 and β = ε), so
        ;; we add nttn1 to the result set directly instead of
        ;; simulating the NFA.
        ;;
        (if (= i -1)
            (aset found nttn1 t)
          (while (<= 0 i)
            (let ((sym (nth i rhs)))
              (fillarray next-states nil)
              (jez-do-set (cur-state cur-states)
                (dolist (leaving-tx (aref state->tx* cur-state))
                  (cl-assert (= (jez-tx-to leaving-tx) cur-state))
                  (when (eq (jez-tx-via leaving-tx) sym)
                    (aset next-states (jez-tx-from leaving-tx) t))
                  (when (= i 0)
                    (let ((nttn (jez-txdb-tx->nttn txdb leaving-tx)))
                      (when nttn
                        (aset found nttn t)))))))
            (cl-psetf cur-states next-states
                      next-states cur-states)
            (decf i)))))
    found))

(defun jez-lr-Dr-impl (txdb nttn)
  "Provide the directly-reads set.
TXDB is a transition database for the LR(0) automaton.  NTTN is a
non-terminal transition number that identifies a transition p
-A-> r.  The function returns a bool-vector describing the set of
terminals that satisfy the following constraint:

  NTTN    = NTTN of p -A-> r
  t       = some terminal
  DR(p,A) = { t ∈ T | p -A-> r -t-> }

The returned bool vector has cardinality equal to the number of
terminals in TXDB's LR.

"
  (let* ((lr (jez-txdb--lr txdb))
         (min-nonterm (jez-lr-min-nonterm lr))
         (Dr (make-bool-vector min-nonterm nil))
         (r (jez-tx-to (jez-txdb-nttn->tx txdb nttn))))
    (jez-dbg "XXX nttn:%S r:%S" nttn r)
    (when (eq nttn 0)
      (aset Dr (jez-lr-end-sym lr) t))
    (dolist (tx (jez-txdb--transitions txdb))
      (when (and (= (jez-tx-from tx) r)
                 (< (jez-tx-via tx) min-nonterm))
        (aset Dr (jez-tx-via tx) t)))
    Dr))

(defun jez-make-lalr-table (lr states txdb)
  "Compute LALR(1) information for LR.

STATES is an ordered vector of states, where each state is an
ordered list of LR(0) items, each item being of the form (PRODNO
. DOTPOS).  The ordering is by jez-lr0-item-<.  The ordering of
items within each state has no significance except to ensure that
equal states are EQUAL.

TXDB is a transaction database.

Return LA.  LA is a hash table mapping each reduce item to a
lookahead set; a lookahead set is a bool vector of size equal to
the number of terminals in LR.
"
  ;; We implement the famous DeRemer and Pennello algorithm for
  ;; near-optimal LALR(1) lookahead set construction.

  ;; N.B. Somewhat confusingly, the "relations" in the paper (in bold
  ;; type in the paper, here ALL CAPS) and the sets (capitalized,
  ;; e.g. Read) are both _functions_: the relations are bool-valued
  ;; functions and the sets (capitalized words) are set-valued
  ;; functions.

  (let* ( ;; Vector mapping symno -> nullability bool
         (nullability (jez-lr-compute-nullability lr))
         (ntt (jez-txdb--ntt txdb))
         (_ (jez-dbg "ntt: %S" ntt))
         (Dr (lambda (nttn)
               (jez-lr-Dr-impl txdb nttn)))
         (READS (lambda (nttn)
                  (jez-lr-READS-impl txdb nullability nttn)))
         (Read (jez-digraph READS Dr (length ntt)))

         ;; Non-terminal transitions indexed by _destination_ state.
         ;; Array maps states to jez-tx objects where the array index
         ;; is the transition's TO field.
         (state->tx*
          (cl-loop
             with state->tx* = (make-vector (length states) nil)
             for tx in (jez-txdb--transitions txdb)
             for to = (jez-tx-to tx)
             do (push tx (aref state->tx* to))
             finally return state->tx*))

         (INCLUDES-table
          (jez-lr-precompute-include-table txdb nullability))

         (INCLUDES (lambda (nttn)
                     (jez-lr-INCLUDES-impl
                      txdb
                      INCLUDES-table
                      state->tx*
                      nttn)))
         (Follow (jez-digraph INCLUDES Read (length ntt)))

         (state->nttn
          (let ((state->nttn (make-vector (length states) nil)))
            (dotimes (nttn (length ntt))
              (push nttn
                    (aref state->nttn
                          (jez-tx-from (aref ntt nttn)))))
            state->nttn))

         (LOOKBACK
          (lambda (q P)
            (jez-lr-LOOKBACK-impl
             q
             P
             state->tx*
             state->nttn
             ntt)))
         (LA (make-hash-table :test 'eq))
         (productions (jez-lr-productions lr))
         (nr-terminals (jez-lr-number-terminals lr)))
    (dotimes (stateno (length states))
      (let ((state (aref states stateno)))
        (dolist (item state)
          (let* ((prodno (jez-lr-item-prodno item))
                 (dotpos (jez-lr-item-dotpos item))
                 (prod (aref productions prodno)))
            ;; If this item is a reduction item --- i.e., dot at end
            ;; --- compute the lookahead set.
            (when (= dotpos (length (cdr prod)))
              ;; LA(q, A→ω) = ∪{ Follow(p,A) | (q, A→ω) LOOKBACK (p,A) }
              ;; Here, `lb' is the number of transition (p,A).
              (let* ((item-LA (make-bool-vector nr-terminals nil)))
                (jez-do-set (lb (funcall LOOKBACK stateno prod))
                  (bool-vector-union
                   item-LA
                   (funcall Follow lb)
                   item-LA))
                (puthash item item-LA LA)))))))
    LA))

(defun jez-make-lr-parser (grammar)
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

  (let* ((rules (first grammar))
         (terminals (second grammar))
         (lr (jez-lr-slurp-grammar rules terminals 'start))))

  )

(cl-defun jez-describe-automaton-dotviz (lr
                                         states
                                         transitions
                                         &key
                                         numbered-states
                                         numbered-ntt
                                         la)
  (let ((productions (jez-lr-productions lr)))
    (princ "digraph {\n")
    (dotimes (stateno (length states))
      (let ((needbr nil)
            (state (aref states stateno)))
        (princ (format "state_%d " stateno))
        (princ "[label=<")
        (when numbered-states
          (princ (format "%d" stateno))
          (setf needbr t))
        (dolist (item state)
          (if needbr
              (princ "<br/>")
            (setf needbr t))
          (let* ((prodno (jez-lr-item-prodno item))
                 (dotpos (jez-lr-item-dotpos item))
                 (prod (aref productions prodno))
                 (lhs (car prod))
                 (rhs (cdr prod)))
            (princ (xml-escape-string (jez-lr-symbol-name lr lhs)))
            (princ "→")
            (dotimes (i (length rhs))
              (when (= i dotpos)
                (princ "•"))
              (princ (xml-escape-string (jez-lr-symbol-name
                                         lr
                                         (nth i rhs)))))
            (when (= dotpos (length rhs))
              (princ "•")

              (when la
                (princ "&nbsp;&nbsp;&nbsp;&nbsp;")
                (let ((item-la (gethash item la)))
                  (cond ((not item-la)
                         (princ "?"))
                        ((= (bool-vector-count-population item-la) 0)
                         (princ "∅"))
                        (t
                         (let ((f t))
                           (jez-do-set (symno item-la)
                             (if f (setf f nil) (princ " "))
                             (princ (xml-escape-string
                                     (jez-lr-symbol-name lr symno))))))))))))
        (princ ">]")
        (princ ";\n")))
    (princ (format "hidden_start [style=invis];\n"))
    (dolist (tx transitions)
      (princ (format "state_%d -> state_%d "
                     (jez-tx-from tx)
                     (jez-tx-to tx)))
      (princ (format "[label=<%s>]"
                     (xml-escape-string
                      (concat
                       ""
                       (jez-lr-symbol-name lr (jez-tx-via tx))))))
      (princ ";\n"))
    (princ (format "hidden_start -> state_0;\n"))
    (princ "}\n")))

(cl-defun jez-view-automaton (lr
                              &key
                              keep-dotfile
                              numbered-states
                              la-type)
  (jez-with-named-temp-file (dotfile "jez-view" nil ".dot")
    (jez-with-named-temp-file (pdffile "jez-view" nil ".pdf")
     (with-temp-file dotfile
       (let* ((lr0info (jez-compute-lr0-states lr))
              (states (nth 0 lr0info))
              (txdb (nth 1 lr0info))
              (la (cl-ecase la-type
                    (:lalr
                     (jez-make-lalr-table lr states txdb))
                    ((nil) nil))))
         (let ((standard-output (current-buffer)))
           (jez-describe-automaton-dotviz
            lr
            states
            (jez-txdb--transitions txdb)
            :numbered-states numbered-states
            :la la))))
     (shell-command (format "dot -Tpdf %s > %s"
                            (shell-quote-argument dotfile)
                            (shell-quote-argument pdffile)))
     (shell-command (format "evince %s 2>/dev/null"
                            (shell-quote-argument pdffile)))
     (when keep-dotfile
       (setf dotfile nil)))))

(provide 'jezebel-lr)
