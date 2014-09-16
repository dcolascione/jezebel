;; -*- lexical-binding: t -*-

;; Fully incremental lexer for Jezebel language environments.
;; Based on the IGLR algorithm in Tim A. Wagner's "Practical
;; Algorithms for Incremental Software Development Environments"
;;
;; This module consists of a generic NFA creation and manipulation
;; system and a set of functions for transforming generic NFA
;; specifications into recognizers and lexers of various sorts.  The
;; lexer is described in the portion of the module dedicated to
;; scanning specifically.
;;
;; The NFA representation we choose is somewhat unusual in that we
;; label state transitions with (predicate, character) pairs instead
;; of just characters.  This representation allows us to represent
;; arbitrary user-specified predicates as restricted ε-transitions.
;; We represent DFAs as restricted NFAs.
;;

(require 'jezebel-util)
(require 'pcase)

(autoload 'xml-escape-string "xml")


;; DFA

;; The input stream is a sequence characters.  It's our job to
;; transform this character sequence into a sequence of tokens, where
;; each token covers one or more characters.  Tokenization (or
;; "lexing") is a highly restricted form of parsing: our left context
;; is restricted to a single integer, the "lex state".  Consequently,
;; we can recognize (without special hacks) only regular languages.
;;
;; Our grammar consists of a set of lex states, and for each lex
;; state, a set of regular expressions to match.  We associate a token
;; identifier and a "next lex state" with each regular expression.  At
;; each possible token start position (the first being bob), we find
;; the regular expression (of those associated with the current lex
;; state) that produces the longest match, report its associated token
;; ID as the token at the current position, and set the lex state to
;; that regular expression's next lex state.  We repeat until we reach
;; the end of the buffer.
;;
;; Buffer modifications do not cause retokenization; instead,
;; modifications merely adjust token boundaries arbitrarily (which
;; happens naturally, as we store token identity information in text
;; properties) and mark modified tokens as inconsistent.  We reconcile
;; the token stream on demand.
;;

(defvar jez-lex-token nil)
(defvar jez-lex-token-id nil)
(defvar jez-lex-token-examined nil)
(defvar jez-lex-token-length nil)

(cl-deftype jez-nfa-state () '(and (not null) symbolp))
(defun jez-nfa-state-create ()
  "Create a new NFA state."
  (cl-gensym "jez-nfa-state"))

(defun jez-nfa-state-tags (state)
  "Return the list of tags associated with STATE."
  (jez-symbol-value state))

(defun jez-nfa-state-copy (state)
  "Create a new NFA state based on existing state STATE."
  (let ((new-state (jez-nfa-state-create)))
    (set new-state (jez-symbol-value state))
    new-state))

(defun jez-nfa-state-merge (states)
  "Merge the semantic information in STATES and create a new state.
Used during DFA creation."
  (cond ((null states)
         (jez-nfa-state-create))
        ((null (cdr states))
         (jez-nfa-state-copy (car states)))
        (t
         (let ((new-state (jez-nfa-state-create)))
           (set new-state
                (let ((new-tags))
                  (dolist (state states)
                    (dolist (tag (jez-nfa-state-tags state))
                      (unless (memq tag new-tags)
                        (push tag new-tags))))
                  (nreverse new-tags)))
           new-state))))

(defun jez-nfa-state-< (a b)
  "Compare two states.  The order is arbitrary but consistent."
  (jez-symbol-< a b))

;; Each edge in our graph is labeled with a "via", which represents a
;; transition between states.  Each via is either a character range a
;; predicate, or :ε.
;;
;; A character range describes a transition over a character.  It is
;; of the form (LB . UB), where LB and UB are characters forming the
;; inclusive lower and upper bounds of the transition range.
;;
;; A predicate edge is a cons of the form (:when SYMBOL) or
;; (:unless SYMBOL), indicating a match or an explicit
;; non-match, respectively, for the identified predicate.
;;
;; A :ε via represents a transition over nothing, as is traditional
;; for NFAs.

(defun jez-nfa-via-p (via)
  "Type test for NFA via objects."
  (or (and (consp via)
           (or (and (integerp (car via))
                    (integerp (cdr via)))
               (and (memq (car via) '(:when :unless))
                    (symbolp (cdr via)))))
      (eq via :ε)))

(cl-deftype jez-nfa-via ()
  '(satisfies jez-nfa-via-p))

(defun jez-nfa-via-create-ε ()
  "Create a via object that represents a transition over nothing."
  :ε)

(defun jez-nfa-via-create-character (lb &optional ub)
  "Create a via object that represents a character transition.
LB is the lower bound of the transition range; UB is the upper.
Bounds are inclusive.  UB defaults to LB."
  (let ((via (cons lb (or ub lb))))
    (cl-check-type via jez-nfa-via)
    via))

(defun jez-nfa-via-create-predicate (predicate)
  "Create a via object that transitions over a zero-width predicate.
PREDICATE must be a cons either of the form (:when PREDICATE)
or (:unless PREDICATE)."
  (cl-assert (memq (car predicate) '(:when :unless)))
  predicate)

(defun jez-nfa-via-ε-p (via)
  "Is VIA an epsilon transition?"
  (eq via :ε))

(defun jez-nfa-via-character-p (via)
  "Is this via a concrete transition over input?"
  (and (consp via)
       (integerp (car via))))

(defun jez-nfa-via-character-range (via)
  (cl-assert (jez-nfa-via-character-p via))
  via)

(defun jez-nfa-via-predicate-p (via)
  "Is this via a predicate pseudo-transition?"
  (and (consp via)
       (memq (car via) '(:when :unless))))

(defun jez-nfa-via-predicate (via)
  "Return the predicate over which VIA transitions."
  (cl-assert (jez-nfa-via-predicate-p via))
  (cdr via))

(defun jez-nfa-tx-create (from via to)
  "Create a new NFA transition.
FROM is the state transitioning from; VIA is a jez-nfa-via, and
TO is the state being transitioned to."
  (cl-check-type from jez-nfa-state)
  (cl-check-type via jez-nfa-via)
  (cl-check-type to jez-nfa-state)
  (cl-list* from via to))

(defun jez-nfa-tx-create-ε (from to)
  "Create a ε-transition."
  (jez-nfa-tx-create from (jez-nfa-via-create-ε) to))

(cl-defsubst jez-nfa-tx-from (tx)
  "Return the state from which TX transitions."
  (car tx))

(cl-defsubst jez-nfa-tx-via (tx)
  "Return the via label for TX.
Return value is a `jez-nfa-via'."
  (cadr tx))

(cl-defsubst jez-nfa-tx-to (tx)
  "Return the state to which TX transitions."
  (cddr tx))

(defun jez-nfa-txset-create (&rest tx-or-txsets)
  "Create a set of transitions.
Each TX-OR-TXSETS is either a transition created by
`jez-nfa-tx-create' or a txset created by `jez-nfa-txset-create'."
  ;; Avoid uselessly copying transition set substructure
  (apply #'list tx-or-txsets))

(defun jez-nfa-txset-walk (txset function)
  "Call FUNCTION for each transition in txset.
FUNCTION accepts one argument: the transition object."
  (cond ((null txset))
        ((listp (car txset))
         (dolist (tx txset)
           (jez-nfa-txset-walk tx function)))
        (t
         (funcall function txset))))
(put 'jez-nfa-txset-walk 'lisp-indent-function 1)

(cl-defstruct (jez-nfa (:constructor jez-nfa--create (start accept txset)))
  "This structure represents a finite automaton.  We actually use
the same representation for deterministic and non-deterministic
finite automata, calling both \"NFA\"s."
  ;; `jez-nfa-state' object representing the first state
  start
  ;; `jez-nfa-state' object representing the last state
  accept
  ;; Transitions possible in this NFA: type is either a transition
  ;; (result of calling `jez-nfa-tx-create') or txset (result of
  ;; calling `jez-nfa-txset-create')
  txset
  ;; We set this flag when incorporating an NFA into another NFA.  If
  ;; an NFA is incorporated more than once, it needs to be deep-copied
  ;; to avoid state aliasing issues.  For example, if we try to match
  ;; "aab", the two "a"s need to be distinct so that the states in the
  ;; second "a" know to transition to a state where we can match "b".
  ;; The routines below call `jez-nfa-unshare' to manage this flag and
  ;; to avoid aliasing problems.
  shared-p
  ;; This flag indicates that this NFA contains only deterministic
  ;; transitions.
  deterministic-p)

(defun jez-nfa-remap-state (state-map state)
  (or (gethash state state-map)
      (puthash state (jez-nfa-state-copy state) state-map)))

(defun jez-nfa-deep-copy (nfa)
  "Return a copy of NFA with no shared substructure.
The copy's shared flag is unset."
  (let ((state-map (make-hash-table :test 'eq))
        (new-transitions nil))
    (jez-nfa-txset-walk (jez-nfa-txset nfa)
      (lambda (tx)
        (let* ((orig-from (jez-nfa-tx-from tx))
               (new-from (jez-nfa-remap-state state-map orig-from))
               (via (jez-nfa-tx-via tx))
               (orig-to (jez-nfa-tx-to tx))
               (new-to (jez-nfa-remap-state state-map orig-to)))
          (push (jez-nfa-tx-create new-from via new-to)
                new-transitions))))
    (jez-nfa--create
     (jez-nfa-remap-state state-map (jez-nfa-start nfa))
     (jez-nfa-remap-state state-map (jez-nfa-accept nfa))
     (nreverse new-transitions))))

(defun jez-nfa-unshare (nfa)
  "Return NFA or an unshared copy.  See comments in `jez-nfa'."
  (if (jez-nfa-shared-p nfa)
      (jez-nfa-deep-copy nfa)
    (setf (jez-nfa-shared-p nfa) t)
    nfa))

(defun jez-nfa-from-via (via)
  "Make an NFA that matches the via V."
  (let* ((start (jez-nfa-state-create))
         (accept (jez-nfa-state-create)))
    (jez-nfa--create start accept (jez-nfa-tx-create start via accept))))

(defun jez-nfa-from-character (c)
  "Make an NFA that matches a character C unconditionally."
  (jez-nfa-from-via (jez-nfa-via-create-character c)))

(defun jez-nfa-from-charset (charset)
  "Make an NFA that matches a CHARSET.
CHARSET can either be a single character, a cons (LB . UB), a
char-table, or a string in traditional regexp character-class
syntax."
  (cond ((characterp charset)
         (jez-nfa-from-character charset))
        ((consp charset)
         (jez-nfa-from-via
          (jez-nfa-via-create-character
           (car charset)
           (cdr charset))))
        ((stringp charset)
         (let ((ranges nil)
               (s (append charset nil)))
           (while s
             (pcase s
               (`(,c1 ?\- ,c2 . ,rest)
                 (push (cons c1 c2) ranges)
                 (setf s rest))
               (`(,c . ,rest)
                 (push c ranges)
                 (setf s rest))))
           (apply #'jez-nfa-union
                  (mapcar #'jez-nfa-from-charset ranges))))
        ((char-table-p charset)
         (let ((ranges nil))
           (map-char-table
            (lambda (r v)
              (when v (push (if (consp r) (cons (car r) (cdr r)) r)
                            ranges)))
            charset)
           (apply #'jez-nfa-union
                  (mapcar #'jez-nfa-from-charset ranges))))
        (t
         (error "unknown charset type: %S" charset))))

(defun jez-nfa-concat (&rest nfa-list)
  "Make an NFA that matches the concatenation of the given NFAs.
If NFA-LIST is empty, return an NFA that matches the empty
string."
  (if (not nfa-list)
      (jez-nfa-empty)
    (let ((nfa-list (mapcar #'jez-nfa-unshare nfa-list)))
      (jez-nfa--create
       (jez-nfa-start (first nfa-list))
       (let ((last-nfa (car (last nfa-list))))
         (jez-nfa-accept last-nfa))
       (apply #'jez-nfa-txset-create
              (cl-loop
                 for prev in nfa-list
                 for next in (cdr nfa-list)
                 collect (jez-nfa-tx-create-ε (jez-nfa-accept prev)
                                              (jez-nfa-start next)))
              (mapcar #'jez-nfa-txset nfa-list))))))

(defun jez-nfa-with-tags (nfa &rest tags)
  "Make an NFA with TAGS in its accept state.
TAGS are arbitrary lisp values; internal NFA machinery may merge
  tags that are `equal'."
  (let ((accept (jez-nfa-state-create)))
    (set accept tags)
    (jez-nfa--create
     (jez-nfa-start nfa)
     accept
     (jez-nfa-txset-create
      (jez-nfa-tx-create-ε (jez-nfa-accept nfa) accept)
      (jez-nfa-txset nfa)))))

(defun jez-nfa-union (&rest nfa-list)
  "Make an NFA that matches the union of the given NFAs.
If NFA-LIST is empty, return an NFA that matches the empty
string."
  (cond
    ((not nfa-list) (jez-nfa-empty))
    ((not (cdr nfa-list)) (car nfa-list))
    (t
     (let* ((nfa-list (mapcar #'jez-nfa-unshare nfa-list))
            (start (jez-nfa-state-create))
            (accept (jez-nfa-state-create)))
       (jez-nfa--create
        start
        accept
        (apply #'jez-nfa-txset-create
               (cl-loop
                  for nfa in nfa-list
                  collect (jez-nfa-tx-create-ε
                           start
                           (jez-nfa-start nfa)))
               (cl-loop
                  for nfa in nfa-list
                  collect (jez-nfa-tx-create-ε
                           (jez-nfa-accept nfa)
                           accept))
               (mapcar #'jez-nfa-txset nfa-list)))))))

(defun jez-nfa-kleene (repeated-nfa)
  "Make an NFA that matches REPEATED-NFA zero or more times."
  (let* ((repeated-nfa (jez-nfa-unshare repeated-nfa))
         (start (jez-nfa-start repeated-nfa))
         (accept (jez-nfa-accept repeated-nfa)))
    (jez-nfa--create
     start
     accept
     (jez-nfa-txset-create
      (jez-nfa-tx-create-ε start accept)
      (jez-nfa-tx-create-ε accept start)
      (jez-nfa-txset repeated-nfa)))))

(defun jez-nfa-repeat (n m repeated-nfa)
  "Make an NFA that matches REPEATED-NFA N to M times inclusive.
Matching zero times meaning matching the empty string."
  (apply #'jez-nfa-union
         (cl-loop
            with template = nil
            for i upto m
            when (<= n i) collect (apply #'jez-nfa-concat template)
            do (push repeated-nfa template))))

(defun jez-nfa-empty ()
  "Make an NFA that matches the empty string."
  (let ((state (jez-nfa-state-create)))
    (jez-nfa--create state state nil)))

(defun jez-nfa-build-recognize-combinators (erx)
  "NFA builder recognizer for NFA combinators.
ERX is an ERX expression; return a `jez-nfa' instance or `nil' if
no construct is recognized."
  (pcase erx
    ;; Concatenation
    (`(,(or `and `: `seq `sequence `submatch `group) . ,atoms)
      (apply #'jez-nfa-concat (mapcar #'jez-nfa-build atoms)))
    (`(,(or `submatch-n `group-n) ,_ . ,atoms)
      (apply #'jez-nfa-concat (mapcar #'jez-nfa-build atoms)))

    ;; Union
    (`(,(or `or `|) . ,choices)
      (apply #'jez-nfa-union (mapcar #'jez-nfa-build choices)))
    (`(maximal-match ,sub-erx)
      (jez-nfa-build sub-erx))

    ;; Kleene star
    (`(,(or `zero-or-more `0+ `*) . ,atoms)
      (let ((repeated-nfa (jez-nfa-build `(: ,@atoms))))
        (jez-nfa-kleene repeated-nfa)))
    (`(,(or `one-or-more `1+ `+) . ,atoms)
      (let ((repeated-nfa (jez-nfa-build `(: ,@atoms))))
        (jez-nfa-concat repeated-nfa (jez-nfa-kleene repeated-nfa))))

    ;; Bounded repetition
    (`(,(or `zero-or-one `optional `opt `\?) . ,atoms)
      (jez-nfa-repeat 0 1 (jez-nfa-build `(: ,@atoms))))
    (`(repeat ,n ,sexp)
      (jez-nfa-repeat n n (jez-nfa-build sexp)))
    (`(= ,n . ,atoms)
      (jez-nfa-repeat n n (jez-nfa-build `(: ,@atoms))))
    (`(>= ,n . ,atoms)
      (let ((repeated-nfa (jez-nfa-build `(: ,@atoms))))
        (jez-nfa-concat (jez-nfa-repeat n n repeated-nfa)
                        (jez-nfa-kleene repeated-nfa))))
    (`(repeat ,n ,m ,sexp)
      (jez-nfa-repeat n m (jez-nfa-build sexp)))
    (`(** ,n ,m . ,atoms)
      (jez-nfa-repeat n m (jez-nfa-build `(: ,@atoms))))

    ;; Non-greedy operators
    ((or `(minimal-match . ,_)
         `(*? . ,_)
         `(+? . ,_)
         `(?? . ,_)
         `(backref ,_))
     (error "unsupported construct: %S" erx))))

(defun jez-nfa-build-recognize-character-atoms (erx)
  "NFA builder recognizer for character atoms.
ERX is an ERX expression; return a `jez-nfa' instance or `nil' if
no construct is recognized."
  (pcase erx
    ;; Actual characters
    ((pred characterp)
     (jez-nfa-from-character erx))
    ((pred stringp)
     (jez-nfa-build `(: ,@erx)))
    ;; Character sets
    ((or `not-newline `nonl)
     (jez-nfa-build `(not (any ?\n))))
    (`anything
     (jez-nfa-build `(in (0 . ,(max-char)))))
    (`(,(or `any `in `char) . ,sets)
      (apply #'jez-nfa-union (mapcar #'jez-nfa-from-charset sets)))
    (`(not (any . ,_sets))
      (error "implement me"))
    ;; String regular expressions
    (`(regexp ,regexp)
      (require 'pcre2el)
      (jez-nfa-build (funcall 'rxt-elisp-to-rx regexp)))))

(defvar jez-nfa-build-recognizers
  '(jez-nfa-build-recognize-combinators
    jez-nfa-build-recognize-character-atoms)
  "List of matchers for erx syntax.")

(defun jez-nfa-build (erx)
  "Build an NFA matcher from extended rx pattern ERX.
ERX patterns re normal `rx' patterns except that atoms can also
be `jez-nfa' instances and some features of `rx' are not
supported.  The unsupported features are:

  * back-references
  * non-greedy operators
  * syntax table queries
  * point, word, and {beginning-,end-}-of-buffer tests

Groups are supported, but group capture is not, so all groups are
treated as shy groups.

The (regex REGEX) facility required the pcre2el library."

  (cl-loop
     for recognizer in jez-nfa-build-recognizers
     for nfa = (funcall recognizer erx)
     when nfa return nfa
     finally do (error "unrecognized construct %S" erx)))

(defun jez-nfa-index-departures (nfa)
  "Make a hash table mapping NFA states to lists of transitions.
Each key in the hash table is an NFA state.  Each value is a list
of transitions that depart from that state."
  (let ((index (make-hash-table :test 'eq)))
    (jez-nfa-txset-walk (jez-nfa-txset nfa)
      (lambda (tx)
        (push tx (gethash (jez-nfa-tx-from tx) index))))
    index))

(defun jez-nfa-reverse-in-place (nfa)
  "Destructively reverse NFA.
If NFA shares substructure with another NFA, behavior is
unspecified.  Return the reversed NFA."
  (when (jez-nfa-deterministic-p nfa)
    ;; A DFA backwards is not necessarily a DFA
    (setf (jez-nfa-deterministic-p nfa) nil))
  (jez-nfa-txset-walk (jez-nfa-txset nfa)
    (lambda (tx)
      (psetf (jez-nfa-tx-from tx) (jez-nfa-tx-to tx)
             (jez-nfa-tx-to tx) (jez-nfa-tx-from tx))))
  (psetf (jez-nfa-accept nfa) (jez-nfa-start nfa)
         (jez-nfa-start nfa) (jez-nfa-accept nfa))
  nfa)


;; DFA construction

(defun jez-nfa-normalize-state-set (state-set)
  "Put STATE-SET in canonical form, destructively."
  (delete-consecutive-dups
   (sort state-set #'jez-nfa-state-<)))

(defun jez-nfa-ε-closure (from->tx states)
  "Find states reachable from STATE by zero or more ε transitions.
FROM->TX is the result of `jez-nfa-index-departures'.  STATES is
a list of state (in arbitrary order) over which to close.  The
returned state set is in canonical order."
  (let ((work-queue states)
        (ε-closure nil))
    (while work-queue
      (let ((from (pop work-queue)))
        (unless (memq from ε-closure)
          (push from ε-closure)
          (dolist (tx (gethash from from->tx))
            (when (jez-nfa-via-ε-p (jez-nfa-tx-via tx))
              (let ((to (jez-nfa-tx-to tx)))
                (push to work-queue)))))))
    (jez-nfa-normalize-state-set ε-closure)))

(defun jez-nfa-predicate-< (a b)
  "Provide a consistent, but arbitrary ordering between predicates."
  (or (jez-symbol-< (car a) (car b))
      (and (eq (car a) (car b))
           (jez-symbol-< (cdr a) (cdr b)))))

(defun jez-nfa-invert-predicate (predicate)
  "Return a predicate that matches when PREDICATE does not."
  (cl-assert (jez-nfa-via-predicate-p predicate))
  (cons (if (eq (car predicate) :when) :unless :when)
        (cdr predicate)))

(defun jez-nfa-merge-predicates (predicates new-predicate)
  "Merge a predicate into a predicate set.
PREIDCATES is an existing predicates set.  NEW-PREDICATE is a
predicate to merge.  Result is either a list of predicates in
canonical form or
:impossible if the resulting list contains contradictory
predicates.  The merge operation may destroy the old value of
PREDICATES."
  (cond ((member new-predicate predicates)
         ;; Predicate already in the list
         predicates)
        ((member (jez-nfa-invert-predicate new-predicate) predicates)
         ;; The list would contain contradictory predicates
         :impossible)
        (t
         ;; Insert predicate into list at correct position.
         (sort (cons new-predicate predicates) #'jez-nfa-predicate-<))))

(defun jez-nfa-p-closure (from->tx states)
  "Build database of states reachable from STATE.
STATES is a list in arbitrary order of NFA states over which to
close; FROM-TX is the result of `jez-nfa-index-departures'.
Reachability is over ε-transitions and predicates.  Return a list
P-CLOSURE, where each element is (PREDICATE-LIST . ε-CLOSURE).
p-closures are not unique; results are not guaranteed to be in
any particular order. "
  (let* ((work-queue (list (cons nil states)))
         (seen work-queue)
         (ε-closures nil))
    (while work-queue
      (let* ((item (pop work-queue))
             (item-predicates (car item))
             (ε-closure (jez-nfa-ε-closure from->tx (cdr item))))
        (push (cons item-predicates ε-closure) ε-closures)
        (dolist (state ε-closure)
          (dolist (tx (gethash state from->tx))
            (let ((via (jez-nfa-tx-via tx)))
              (when (jez-nfa-via-predicate-p via)
                (let* ((ps (jez-nfa-merge-predicates item-predicates via)))
                  (unless (eq ps :impossible)
                    (let ((new-item (cons ps (jez-nfa-tx-to tx))))
                      (unless (member new-item seen)
                        (push new-item seen)
                        (push new-item work-queue)))))))))))
    ε-closures))

(defun jez-nfa-collect-predicates (p-closure)
  "Collect the predicate symbols used in P-CLOSURE.
P-CLOSURE is a data structure `jez-nfa-p-closure' returns.  The
returned list contains no duplicates and is ordered according to
`jez-symbol-<'."
  (let ((predicates))
    (dolist (item p-closure)
      (dolist (predicate (car item))
        (let ((predicate-symbol (jez-nfa-via-predicate predicate)))
          (unless (memq predicate-symbol predicates)
            (push predicate-symbol predicates)))))
    (sort predicates #'jez-symbol-<)))

(defun jez-nfa-p-closure-derivative (p-closure given)
  "Evaluate P-CLOSURE with respect to predicates GIVEN.
GIVEN is a list (in arbitrary order) of predicates.  Return the
ε-closure of resulting states in P-CLOSURE that are reachable
when the given predicates are true."
  (jez-nfa-normalize-state-set
   (cl-loop
      for (x-predicates . x-closure) in p-closure
      when (cl-loop
              for x-predicate in x-predicates
              always (member x-predicate given))
      append x-closure)))

(defun jez-nfa-p-closure-to-p-tree-1 (p-closure predicates given)
  "Recursive helper for `jez-nfa-p-closure-p-tree'."
  (if predicates
      (let ((this-predicate (car predicates)))
        (cl-list* this-predicate
                  (jez-nfa-p-closure-to-p-tree-1
                   p-closure
                   (cdr predicates)
                   (cons this-predicate given))
                  (jez-nfa-p-closure-to-p-tree-1
                   p-closure
                   (cdr predicates)
                   (cons (jez-nfa-invert-predicate this-predicate)
                         given))))
    (cons :ε (jez-nfa-p-closure-derivative p-closure given))))

(defun jez-nfa-p-closure-to-p-tree (p-closure)
  "Generate a decision tree from P-CLOSURE.
A decision tree is a flattened representation of the outcomes of
evaluating P-CLOSURE against all possible predicates.  Each node
in the tree is either (:ε . ε-CLOSURE) or (PREDICATE WHEN-CASE
UNLESS-CASE), where WHEN-CASE and UNLESS-CASE are themselves tree
nodes."
  (jez-nfa-p-closure-to-p-tree-1
   p-closure
   (jez-nfa-collect-predicates p-closure)
   nil))

(defun jez-nfa-txmap (from->tx states)
  "Generate a non-overlapping map of outbound character transitions.
FROM->TX is the result of calling `jez-nfa-index-departures';
STATES is the set of NFA states to consider.  We return a list in
which each item is (VIA . DESTINATION-STATES), where VIA is a
character range via and DESTINATION-STATES is a set of states to
states in STATES can transition on the characters encoded in
VIA."
  (let ((outbound nil))
    (dolist (state states)
      (dolist (tx (gethash state from->tx))
        (let ((via (jez-nfa-tx-via tx)))
          (when (jez-nfa-via-character-p via)
            (push (list (jez-nfa-via-character-range via)
                        (jez-nfa-tx-to tx))
                  outbound)))))
    (jez-combine-ranges outbound)))

(defun jez-nfa-make-dfa-1 (nfa)
  "Make a DFA based on NFA using the standard subset construction.
Informally, return a `jez-nfa' object contains only deterministic
transitions.  More specifically, the returned NFA obeys the
following invariants:

  1) The transitions from each state all consist either of
     character ranges, predicates, or ε-transitions to the accept
     state.

  2) Predicate states have at most two outbound transitions: one
     for a given predicate's success and one for the given
     predicate's failure.

  3) A given character leads to at most one outbound transition
     from a given state.

These constraints make it feasible to directly construct matching
tables from the resulting DFA.  Transitions from a given state
are either all characters or a single predicate.  Matchers are
expected to follow all predicate edges after transitioning over
an input character."
  (let* ((from->tx (jez-nfa-index-departures nfa))
         (dfa-transitions nil)
         (dfa-states (make-hash-table :test 'equal))
         (work-queue nil))
    (cl-labels
        ((p-enqueue (p-tree)
           (or (gethash p-tree dfa-states)
               (let ((new-state
                      (cond ((eq (car p-tree) :ε)
                             (puthash p-tree
                                      (jez-nfa-state-merge (cdr p-tree))
                                      dfa-states))
                            (t
                             (puthash p-tree
                                      (jez-nfa-state-create)
                                      dfa-states)))))
                 (push (cons new-state p-tree) work-queue)
                 new-state)))
         (enqueue (states)
           (p-enqueue
            (jez-nfa-p-closure-to-p-tree
             (jez-nfa-p-closure from->tx states)))))
      (let* ((dfa-start (enqueue (list (jez-nfa-start nfa))))
             (nfa-accept (jez-nfa-accept nfa))
             (dfa-accept (jez-nfa-state-copy nfa-accept)))
        (while work-queue
          (cl-destructuring-bind (dfa-state . p-tree) (pop work-queue)
            (cond ((eq (car p-tree) :ε)
                   (let ((closure (cdr p-tree)))
                     (dolist (outbound (jez-nfa-txmap from->tx closure))
                       (push (jez-nfa-tx-create
                              dfa-state
                              (jez-the jez-nfa-via (car outbound))
                              (enqueue (cdr outbound)))
                             dfa-transitions))
                     ;; Mark accept states by adding ε-transitions to
                     ;; the new accept state.  These are the only
                     ;; ε-transitions in the resulting DFA.
                     (when (memq nfa-accept closure)
                       (push (jez-nfa-tx-create-ε dfa-state dfa-accept)
                             dfa-transitions))))
                  (t (cl-destructuring-bind (predicate yes . no) p-tree
                       (push (jez-nfa-tx-create
                              dfa-state
                              predicate
                              (p-enqueue yes))
                             dfa-transitions)
                       (push (jez-nfa-tx-create
                              dfa-state
                              (jez-nfa-invert-predicate predicate)
                              (p-enqueue no))
                             dfa-transitions))))))
        (jez-nfa--create
         dfa-start
         dfa-accept
         dfa-transitions)))))

(defun jez-nfa-make-dfa (nfa &optional unminimized)
  "Make a DFA based on NFA using the standard subset construction.
Return a `jez-nfa' object contains only deterministic
transitions.  The returned DFA contains ε-transitions from all
final states to the accepting state.  If UNMINIMIZED is
non-`nil', do not minimize the number of states in the returned
DFA.  If NFA is already deterministic, return it unchanged."
  (if (jez-nfa-deterministic-p nfa) nfa
    (let ((dfa (if unminimized
                   (jez-nfa-make-dfa-1 nfa)
                 ;; Apply Brzozowski's algorithm to minimize the DFA.
                 ;; By reversing the DFA (producing an NFA again) and
                 ;; building a DFA out of that, we produce a minimized
                 ;; DFA for the reverse language, and by applying this
                 ;; operation a second time, we produce a minimal DFA
                 ;; for our original language.
                 (jez-nfa-make-dfa-1
                  (jez-nfa-reverse-in-place
                   (jez-nfa-make-dfa-1
                    (jez-nfa-reverse-in-place
                     (jez-nfa-make-dfa-1 nfa))))))))
      (setf (jez-nfa-deterministic-p dfa) t)
      dfa)))


;; Misc

(defun jez-nfa-describe-via (via)
  (concat
   (cond ((jez-nfa-via-ε-p via) "ε")
         ((jez-nfa-via-predicate-p via)
          (format "%S" via))
         ((eql (car via) (cdr via))
          (jez-safe-char-format (car via)))
         (t (format "%s-%s"
                    (jez-safe-char-format (car via))
                    (jez-safe-char-format (cdr via)))))))

(defun jez-nfa-number-states (nfa)
  "Assign numbers to states in NFA.
Return a hash table mapping states to their state numbers.  State
numbers begin at zero, which is always the state number for the
starting state."
  (let ((state->stateno (make-hash-table :test 'eq))
        (stateno 0))
    (puthash (jez-nfa-start nfa) 0 state->stateno)
    (jez-nfa-txset-walk (jez-nfa-txset nfa)
      (lambda (tx)
        (let ((from (jez-nfa-tx-from tx))
              (to (jez-nfa-tx-to tx)))
          (unless (gethash from state->stateno)
            (puthash from (incf stateno) state->stateno))
          (unless (gethash to state->stateno)
            (puthash to (incf stateno) state->stateno)))))
    (let ((accept (jez-nfa-accept nfa)))
      (unless (gethash accept state->stateno)
        (puthash accept (incf stateno) state->stateno)))
    state->stateno))

(cl-defun jez-describe-nfa-dotviz (nfa)
  (let* ((state-numbers (make-hash-table :test 'eq))
         (next-stateno -1)
         (intern-state
          (lambda (state)
            (or (gethash state state-numbers)
                (progn
                  (let* ((sn (incf next-stateno))
                         (label (cond ((eq state (jez-nfa-start nfa))
                                       "START")
                                      ((eq state (jez-nfa-accept nfa))
                                       "ACCEPT")
                                      (t sn)))
                         (label (if (not (jez-nfa-state-tags state))
                                    label
                                  (format "%s\n%S" label
                                          (jez-nfa-state-tags state)))))
                    (princ (format "state_%d [label=%s];\n" sn label))
                    (puthash state sn state-numbers))))))
         (work-queue (list (jez-nfa-start nfa)))
         (from->tx (jez-nfa-index-departures nfa))
         (seen (make-hash-table :test 'eq)))
    (princ "digraph {\n")
    (while work-queue
      (let ((state (pop work-queue)))
        (unless (gethash state seen)
          (puthash state t seen)
          (dolist (tx (gethash state from->tx))
            (princ (format "state_%d -> state_%d [label=<%s>];\n"
                           (funcall intern-state (jez-nfa-tx-from tx))
                           (funcall intern-state (jez-nfa-tx-to tx))
                           (xml-escape-string
                            (jez-nfa-describe-via (jez-nfa-tx-via tx)))))
            (push (jez-nfa-tx-to tx) work-queue)))))
    (princ "}\n")
    nil))

(cl-defun jez-view-nfa (nfa &key background debug)
  (jez-run-command "exec xdot"
                   :name "jez-view-nfa"
                   :input (with-output-to-string
                              (jez-describe-nfa-dotviz nfa))
                   :background background
                   :debug debug))

(cl-defstruct (jez-nfa-simple-automaton
                (:constructor jez-nfa-simple-automaton--create))
  ;; Current state number (0 is the starting state)
  state
  ;; Array mapping state numbers to functions to call on entry to each
  ;; state.
  entry-functions
  ;; Array mapping state numbers to char tables.  Each char
  ;; table maps to the next state number.
  transitions)

(defun jez-nfa-simple-automaton-create (nfa)
  "Create a simple automaton for matching NFA.
 This automaton accepts symbols one at a time and either
transitions to a new state or fails.  It is primarily useful for
testing the NFA engine."
  (let* ((dfa (jez-nfa-make-dfa nfa))
         (state->stateno (jez-nfa-number-states dfa))
         (nr-states (hash-table-count state->stateno))
         (entry-functions (make-vector nr-states nil))
         (transitions (make-vector nr-states nil)))
    (jez-nfa-txset-walk (jez-nfa-txset dfa)
      (lambda (tx)
        (let ((via (jez-nfa-tx-via tx)))
          (cond ((jez-nfa-via-character-p via)
                 (let* ((from (jez-nfa-tx-from tx))
                        (from-sn (gethash from state->stateno))
                        (ct (or (aref transitions from-sn)
                                (aset transitions
                                      from-sn
                                      (make-char-table nil))))
                        (to (jez-nfa-tx-to tx))
                        (to-sn (gethash to state->stateno))
                        (char-range (jez-nfa-via-character-range via)))
                   (set-char-table-range ct char-range to-sn)))
                ((jez-nfa-via-predicate-p via)
                 (error "implement me"))))))
    (maphash
     (lambda (state stateno)
       (unless (aref transitions stateno)
         (setf (aref transitions stateno) (make-char-table nil)))
       (setf (aref entry-functions stateno) (jez-nfa-state-tags state)))
     state->stateno)
    (jez-nfa-simple-automaton--create
     :state nil
     :entry-functions entry-functions
     :transitions transitions)))

(defun jez-nfa-simple-automaton-reset (automaton)
  "Reset a simple automaton to its start state."
  (setf (jez-nfa-simple-automaton-state automaton) 0)
  (mapc #'funcall
        (aref (jez-nfa-simple-automaton-entry-functions automaton) 0)))

(defun jez-nfa-simple-automaton-transition (automaton c)
  "Transition AUTOMATON to a new state on C.
C is a character.  Return the new state or nil for failure."
  (let* ((state (jez-nfa-simple-automaton-state automaton))
         (transitions (jez-nfa-simple-automaton-transitions automaton))
         (ct (aref transitions state))
         (next-state (aref ct c)))
    (if (not next-state)
        nil
      (mapc #'funcall
            (aref (jez-nfa-simple-automaton-entry-functions automaton)
                  next-state))
      (setf (jez-nfa-simple-automaton-state automaton) next-state))))

(cl-defstruct (jez-lexer-ruleset
                (:constructor jez-lexer-ruleset--create)))

(defun jez-lex-ruleset-create (_productions)
  "Build a lexeer rule set.
PRODUCTIONS is a list of productions of the form

  (TOKEN PATTERN)

where TOKEN is a symbol naming the production and PATTERN is
valid input to `jez-nfa-build'.  `jex-lex-create' accepts a rule
set to build a lexer.  Return a `jez-lexer-ruleset' instance."
  
  )

(defun jez-lex-ruleset-goal (_ruleset _erx)
  "Make a lexer control pattern.
RULESET is a `jez-lex-ruleset' instance; ERX is a pattern
expression." )

(defun jez-lex-create (_ruleset &key _goal)
  "Build a lexer.
RULESET is a set of rules compiled with `jez-lex-create-ruleset'.
GOAL if non-`nil' is a special DFA over the rules.  Return a
`jez-lexer' instance." )

(cl-defstruct jez-lexer ())

(defun jez-lex-configure ()
  "Set up automatic incremental lexing for the current buffer."

  )

(provide 'jezebel-lex)
