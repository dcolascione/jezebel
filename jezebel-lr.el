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
  produces

  ;; Array mapping (- SYMNO MIN-NONTERM) to FIRST int-sets.  The
  ;; entries in each set are terminal symnos.  Created lazily; query
  ;; with jez-lr-FIRST-1.  (We need only the non-terminals because the
  ;; FIRST set of a terminal t is always just { t }).
  FIRST-info

  

  )

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

(defun jez-lr-rhs-for-prodno (lr prodno)
  "Return the RHS for a production number"
  (cdr (aref (jez-lr-productions lr) prodno)))

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

(put 'jez-do-int-set 'lisp-indent-function 1)

(defstruct (jez-lr-state
            (:constructor jez-make-lr-state)
            (:copier nil))
  items)

(defstruct (jez-lr-item
            (:constructor jez-make-lr-item)
            (:copier nil)
            (:type vector))
  (prodno :readonly t) ; Production number in lr
  (dotpos :readonly t) ; Position of dot in production
  (lahead :readonly t) ; Lookahead terminal or nil
  )

(defun jez-lr-item-< (a b)
  "Compare two jez-lr-item instances."

  (cond
   ((< (aref a 0) (aref b 0)))
   ((> (aref a 0) (aref b 0)) nil)
   ((< (aref a 1) (aref b 1)))
   ((> (aref a 1) (aref b 1)) nil)
   ((and (null (aref a 2)) (aref b 2)))
   ((and (aref a 2)
         (aref b 2)
         (< (aref a 2) (aref b 2))))))

(defun jez-lr-state-add-item (lrs item)
  "Add ITEM to a jez-lr-state if not already present.

If item was not present, return non-nil.  Caller promises not to
modify ITEM."
  (let ((items (jez-lr-state-items lrs)))
    (unless (member item items)
      (setf (jez-lr-state-items lrs)
            (sort (cons item items)
                  #'lez-lr-item-<)))))

(defun jez-lr-FIRST (lr symnos)
  "Compute FIRST for a non-empty symbol list SYMNOS.  Return an
int-set; numbers in the int-set are terminals, or jez-epsilon-sym
for the empty production."

  (let (symno first saw-epsilon)
    (setf first (jez-make-int-set))
    (while symnos
      (setf symno (car symnos)
            symnos (cdr symnos))

      (let* ((sym-first (jez-lr-FIRST-1 lr symno))
             (sym-makes-epsilon (jez-int-set-member-p
                                 sym-first
                                 jez-epsilon-sym)))

        ;; Merge this symbol's FIRST set into the one we're
        ;; accumulating.

        (jez-int-set-union first sym-first)

        ;; If symbol is the last one and it makes epsilon, then all
        ;; symbols have produced epsilon and we can leave epsilon in
        ;; our output set.

        (when sym-makes-epsilon
          (setf saw-epsilon t))

        ;; If this symbol cannot produce epsilon, we don't have to
        ;; consider any of the remaining symbols (since none of the
        ;; remaining symbols can be first: we must produce at least
        ;; one terminal for the current symbol.)
        ;;
        ;; Break out of the loop.

        (when (not sym-makes-epsilon)
          (when saw-epsilon
            (jez-int-set-remove first jez-epsilon-sym))
          (setf symnos nil))))

    first))

(defun jez-lr-generate-FIRST-info (lr)
  "Regenerate the FIRST table for LR.
Returns the FIRST information table.  Does not modify LR."

  (let* ((min-nonterm (jez-lr-min-nonterm lr))
         (ftnr (length (jez-lr-produces lr)))
         (productions (jez-lr-productions lr))
         (ft (make-vector ftnr nil)))

    ;; Initialize all sets to empty

    (loop for i below ftnr
          do (aset ft i (jez-make-int-set)))

    ;; Loop over the production rules and add entries to FIRST sets
    ;; until things stop changing.  For RHSes that begin with a
    ;; terminal, we add that terminal to FIRST[LHS].  RHSes that begin
    ;; with non-terminals propagate these terminals to their LHSes.
    ;; In this way, as we loop, FIRST sets naturally migrate from
    ;; right to left.

    (while
        (loop with changed = nil
              for (lhs rhs1 . _) across productions
              for lhs-FIRST = (aref ft (- lhs min-nonterm))
              do (setf changed
                       (or (if (< rhs1 min-nonterm)
                               (jez-int-set-add lhs-FIRST rhs1)
                             (jez-int-set-union
                              lhs-FIRST
                              (aref ft (- rhs1 min-nonterm))))
                           changed))
              finally return changed))
    ft))

(defun jez-lr-FIRST-1 (lr symno)
  "Compute FIRST for just one symbol, terminal or non-terminal.
Return an int-set; numbers in the int-set are terminals, or
jez-epsilon-sym for the empty production.
"

  (let ((min-nonterm (jez-lr-min-nonterm lr)))
    (cond ((< symno min-nonterm)
           (jez-make-int-set (list symno)))
          (t
           (let ((FIRST-info (jez-lr-FIRST-info lr)))
             (unless FIRST-info
               (setf FIRST-info (jez-lr-generate-FIRST-info lr))
               (setf (jez-lr-FIRST-info lr) FIRST-info))
             (aref FIRST-info (- symno min-nonterm)))))))

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

(defun jez-compute-lr0-states (lr)
  "Compute the LR(0) DFA for grammar LR.
Return (STATES . TRANSITIONS).

STATES is an ordered list of states, where each state is an
ordered list of LR(0) items, each item being of the form (PRODNO
. DOTPOS).

TRANSITIONS is an un-ordered list of transitions of the
form (STATENO TERMNO NEW-STATENO), where STATENO is the current
state, TERMNO is the symbol on which to transition, and
NEW-STATENO is the number of the state to which to transition.
The number of a state is its position in STATES."

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

          (push (list current-stateno symno next-stateno) transitions))))

    ;; Done.  Reverse the state list because we accumulated it by
    ;; consing onto the front instead of appending to the end.

    (list (nreverse state-list) (nreverse transitions))))

(defun jez-lr-nclosure-1 (lr items)
  "Run one iteration of the closure algorithm.
Return a list of items to add to items."

  (let (to-add)
    (dolist (item items to-add)
      (let* ((dotpos (jez-lr-item-dotpos item))
             (rhstail (nthcdr dotpos
                              (jez-lr-rhs-for-prodno
                               lr
                               (jez-lr-item-prodno item))))
             (next-symno (car rhstail))
             (item-lahead (jez-lr-item-lahead item)))

        (dolist (next-prodno
                 (jez-lr-production-rules-for-symbol lr next-symno))

          (let* ((la-next-string (append (cdr rhstail) (list item-lahead)))
                 (la-next-set (jez-lr-FIRST lr la-next-string)))

            (jez-do-int-set (la-next la-next-set)
              (let ((new-item (jez-make-lr-item :prodno next-prodno
                                                :dotpos 0
                                                :lahead la-next)))

                (unless (or (member new-item items)
                            (member new-item to-add))
                  (push new-item to-add))))))))))

(defun jez-lr-nclosure (lr lrs)
  "Destructively augment LRS with its LR-closure.
LR is the lr-parsing object providing state information."

  (loop with items = (jez-lr-state-items lrs)
        for to-add = (jez-lr-nclosure-1 lr items)
        while to-add
        do (setf items (append to-add items))
        finally return
        (progn
          (setf (jez-lr-state-items lrs)
                (sort items #'jez-lr-item-<))
          lrs)))

(defun jez-lr-goto (lr lrs X)
  "Compute the goto set of the given item set.
Return a new, independent item set that is already closed over."

  (let ((J (jez-make-lr-state))
        (productions (jez-lr-productions lr)))

    ;; In this construction, items and guaranteed to be sorted and
    ;; unique already, so we can just use the output of this loop
    ;; directly as our new state's item set.

    (setf (jez-lr-state-items J)
          (loop for item in (jez-lr-state-items lrs)
                for rhs = (cdr (aref productions (jez-lr-item-prodno item)))
                if (eq (nth (jez-lr-item-dotpos item) rhs) X)
                collect (jez-make-lr-item
                         :prodno (jez-lr-item-prodno item)
                         :dotpos (1+ (jez-lr-item-dotpos item))
                         :lahead (jez-lr-item-lahead item))))

    (jez-lr-nclosure lr J)
    J))

(defun jez-lr-make-lr1-states (lr)
  "Build an LR parse table using the LR(1) algorithm.
Return an array describing the LR parse automaton, indexed by
state number, with the start state being zero.

Each entry in the array is an alist (LAHEAD . ACTIONS), where
ACTIONS is a list of ACTIONs to perform when the look-ahead token
is LAHEAD (a terminal symbol number).

Each ACTION is either (shift N), (reduce R), error, or accept,
where N is a new state number and R is the production number of a
rule by which to reduce.

"

  (let (C U lrs nsymbols next-state)

    ;; Create the initial LR state.

    (setf lrs (jez-make-lr-state
               :items (list (jez-make-lr-item
                             :prodno 0
                             :dotpos 0
                             :lahead jez-end-sym))))

    (jez-lr-nclosure lr lrs)

    ;; Keep track of states we've already added.  Equal states are
    ;; guaranteed to be EQUAL.

    (push lrs U)
    (setf C (make-hash-table :test 'equal))
    (setf nsymbols (jez-lr-number-symbols lr))

    ;; Keep adding LR states to the queue as long as we find new
    ;; states.  The outer loop terminates because we eventually
    ;; generate all states.

    (while U
      (setf lrs (pop U))
      (puthash lrs t C)
      (dotimes (symno nsymbols)
        (setf next-state (jez-lr-goto lr lrs symno))
        (when (and (not (null (jez-lr-state-items next-state)))
                   (not (gethash next-state C)))
          (push next-state U))))

    (loop for x being the hash-keys of C
          collect x)))

(defun jez-lr-lisp-symbol-for-symno (lr symno)
  "Find the lisp symbol for symbol numbered SYMNO in LR."

  (catch 'found
    (maphash
     (lambda (k v)
       (when (eq v symno)
         (throw 'found k)))
     (jez-lr-sym->symno lr))
    (error "could not find symbol for symno %s" symno)))

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
