;; -*- lexical-binding: t -*-
;; Fully incremental lexer for Jezebel language environments.
;; Based on the IGLR algorithm in Tim A. Wagner's "Practical
;; Algorithms for Incremental Software Development Environments"

(require 'jezebel-util)
(require 'pcase)

(autoload 'xml-escape-string "xml")

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
  "Merge the semantic information in STATES.
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
  (< (sxhash a) (sxhash b)))

(defun jez-nfa-char-range-p (cr)
  (and (consp cr)
       (characterp (car cr))
       (characterp (cdr cr))
       (<= (car cr) (cdr cr))))

;; Transitions between states are labeled with the characters that
;; cause these transitions; these labels can either be single
;; characters or char-table instances describing ranges of characters.
(cl-deftype jez-nfa-edge ()
  '(or characterp char-table-p
    (satisfies jez-nfa-char-range-p)
    (member :ε)))

(defun jez-nfa-tx-create (from via to)
  "Create a new NFA transition.
FROM is the state transitioning from; VIA is a jez-nfa-edge, and
TO is the state being transitioned to."
  (cl-check-type from jez-nfa-state)
  (cl-check-type via jez-nfa-edge)
  (cl-check-type to jez-nfa-state)
  (cl-list* from via to))

(cl-defsubst jez-nfa-tx-from (tx)
  "Return the state from which TX transitions."
  (car tx))

(cl-defsubst jez-nfa-tx-via (tx)
  "Return the edge label for TX.
Return value is a `jez-nfa-edge'."
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

(defun jez-nfa-deep-copy (nfa &optional reverse)
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

(defun jez-nfa-character (c)
  "Make an NFA that matches a character C."
  (let* ((start (jez-nfa-state-create))
         (accept (jez-nfa-state-create)))
    (jez-nfa--create start accept (jez-nfa-tx-create start c accept))))

(defun jez-nfa-from-via (v)
  "Make an NFA that matches the via V."
  (cond ((or (characterp v) (consp v))
         (jez-nfa-character v))
        ((char-table-p v)
         (jez-nfa-character v))
        (t (error "unknown via %S" v))))

(defun jez-nfa-charsets-to-char-table (charsets)
  (let ((char-table (make-char-table nil)))
    (dolist (charset charsets)
      (pcase charset
        ((pred characterp)
         (set-char-table-range char-table (cons charset charset) t))
        ((pred stringp)
         (let ((s (append charset nil)))
           (while s
             (pcase s
               (`(,c1 ?\- ,c2 . ,rest)
                 (set-char-table-range char-table (cons c1 c2) t)
                 (setf s rest))
               (`(,c . ,rest)
                 (set-char-table-range char-table (cons c c) t)
                 (setf s rest))))))
        (`(,from . ,to)
          (set-char-table-range char-table charset t))
        (_ (error "unrecognized charset %S" charset))))
    char-table))

(defun jez-nfa-via-charsets (&rest charsets)
  "Make a graph edge label that matches the union of CHARSETS.
Each CHARSET is either a character, a string in the form
\"A-BCD\", a cons (A . B), or a symbol naming a character class.
If no charsets are given, match the empty string."
  (jez-nfa-charsets-to-char-table charsets))

(defun jez-nfa-via-charsets-negated (&rest charsets)
  "Make a graph edge label that matches everything but CHARSETS.
See `jez-nfa-via-charses' for a description of the allowable
values of CHARSETS."
  (jez-invert-char-table
   (jez-nfa-charsets-to-char-table charsets)))

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
                 collect (jez-nfa-tx-create
                          (jez-nfa-accept prev)
                          :ε
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
      (jez-nfa-tx-create (jez-nfa-accept nfa) :ε accept)
      (jez-nfa-txset nfa)))))

(defun jez-nfa-union (&rest nfa-list)
  "Make an NFA that matches the union of the given NFAs.
If NFA-LIST is empty, return an NFA that matches the empty
string."
  (if (not nfa-list)
      (jez-nfa-empty)
    (let* ((nfa-list (mapcar #'jez-nfa-unshare nfa-list))
           (start (jez-nfa-state-create))
           (accept (jez-nfa-state-create)))
      (jez-nfa--create
       start
       accept
       (apply #'jez-nfa-txset-create
              (cl-loop
                 for nfa in nfa-list
                 collect (jez-nfa-tx-create start
                                            :ε
                                            (jez-nfa-start nfa)))
              (cl-loop
                 for nfa in nfa-list
                 collect (jez-nfa-tx-create (jez-nfa-accept nfa)
                                            :ε
                                            accept))
              (mapcar #'jez-nfa-txset nfa-list))))))

(defun jez-nfa-kleene (repeated-nfa)
  "Make an NFA that matches REPEATED-NFA zero or more times."
  (let* ((repeated-nfa (jez-nfa-unshare repeated-nfa))
         (start (jez-nfa-start repeated-nfa))
         (accept (jez-nfa-accept repeated-nfa)))
    (jez-nfa--create
     start
     accept
     (jez-nfa-txset-create
      (jez-nfa-tx-create start :ε accept)
      (jez-nfa-tx-create accept :ε start)
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
     (jez-nfa-character erx))
    ((pred stringp)
     (jez-nfa-build `(: ,@erx)))
    ;; Character sets
    ((or `not-newline `nonl)
     (jez-nfa-build `(not (any ?\n))))
    (`anything
     (jez-nfa-build `(in (0 . ,(max-char)))))
    (`(,(or `any `in `char) . ,sets)
      (jez-nfa-from-via (apply #'jez-nfa-via-charsets sets)))
    (`(not (any . ,sets))
      (jez-nfa-from-via (apply #'jez-nfa-via-charsets-negated sets)))
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

(defun jez-nfa-ε-closure (from->tx states)
  "Find states reachable from STATES by zero or more ε transitions.
FROM->TX is the result of `jez-nfa-index-departures'.  STATES is
a list of states to close over; it is unordered and may contain
dupliates.  The returned list is in canonical order."
  (let ((work-queue states)
        (ε-closure nil))
    (while work-queue
      (let ((from (pop work-queue)))
        (unless (memq from ε-closure)
          (push from ε-closure)
          (dolist (tx (gethash from from->tx))
            (when (eq (jez-nfa-tx-via tx) :ε)
              (let ((to (jez-nfa-tx-to tx)))
                (push to work-queue)))))))
    (sort ε-closure #'jez-nfa-state-<)))

(defun jez-nfa-map-via-ranges (via function)
  "Enumerate NFA transition edge labels to char ranges.
Call FUNCTION with one argument, a cons (LB . UB), giving the
inclusive lower and upper bounds of the character range
enumerated.  The cons is volatile; to guarantee its value, copy
it."
  (cond ((characterp via)
         (funcall function (cons via via)))
        ((jez-nfa-char-range-p via)
         (funcall function via))
        ((char-table-p via)
         (map-char-table
          (lambda (range v)
            (when (characterp range)
              (setf range (cons range range)))
            (when v
              (funcall function range)))
          via))
        (t (error "unrecognized character range %S" via))))
(put 'jez-nfa-map-via-ranges 'lisp-indent-function 1)

(defun jez-nfa-closure-txmap (from->tx closure)
  "Find outgoing transitions from states in CLOSURE.
STATES is a list of NFA states; FROM-TX is the result of
`jez-nfa-index-departures'.  Group the transitions by their edge
labels; return an alist mapping edge labels to sets of states
reachable by transitions from one of the states in STATES."
  (jez-combine-ranges
   (let (ctx)
     (dolist (from closure)
       (dolist (tx (gethash from from->tx))
         (let ((via (jez-nfa-tx-via tx)))
           (unless (eq via :ε)
             (let ((to (jez-nfa-tx-to tx)))
               (jez-nfa-map-via-ranges via
                 (lambda (bounds)
                   (push (list (cons (car bounds)
                                     (cdr bounds))
                               to)
                         ctx))))))))
     ctx)))

(defun jez-nfa-make-dfa-1 (nfa)
  "Make a DFA based on NFA using the standard subset construction.
Return a `jez-nfa' object contains only deterministic
transitions.  The returned DFA contains ε-transitions from all
final states to the accepting state."
  (let* ((from->tx (jez-nfa-index-departures nfa))
         (start-closure (jez-nfa-ε-closure
                         from->tx
                         (list (jez-nfa-start nfa))))
         (nfa-accept (jez-nfa-accept nfa))
         (dfa-accept (jez-nfa-state-create))
         (dfa-transitions nil)
         ;; Map ε-closures to DFA states
         (dfa-states (make-hash-table :test 'equal))
         ;; Closures to process; enqueue-closure adds new DFA states
         ;; to this list as we see them.
         (work-queue nil))
    (cl-flet ((enqueue-closure (closure)
                (or (gethash closure dfa-states)
                    (let ((new-dfa-state (jez-nfa-state-merge closure)))
                      (puthash closure new-dfa-state dfa-states)
                      (push closure work-queue)
                      new-dfa-state))))
      (enqueue-closure start-closure)
      (while work-queue
        (let* ((closure (pop work-queue))
               (dfa-state (gethash closure dfa-states)))
          (dolist (raw-tx (jez-nfa-closure-txmap from->tx closure))
            (push (jez-nfa-tx-create
                   dfa-state
                   (car raw-tx)
                   (enqueue-closure
                    (jez-nfa-ε-closure from->tx (cdr raw-tx))))
                  dfa-transitions))
          (when (memq nfa-accept closure)
            (push (jez-nfa-tx-create dfa-state :ε dfa-accept)
                  dfa-transitions)))))
    (jez-nfa--create
     (gethash start-closure dfa-states)
     dfa-accept
     dfa-transitions)))

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

(defun jez-nfa-describe-via (via)
  (if (eq via :ε) "ε"
    (let ((pieces))
      (jez-nfa-map-via-ranges via
        (lambda (range)
          (let ((from (car range)) (to (cdr range)))
            (push (if (eql from to)
                      (format "%s" (jez-safe-char-format from))
                    (format "%s-%s"
                            (jez-safe-char-format from)
                            (jez-safe-char-format to)))
                  pieces))))
      (mapconcat #'identity (nreverse pieces) ", "))))

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
        (unless (eq (jez-nfa-tx-via tx) :ε)
          (let* ((from (jez-nfa-tx-from tx))
                 (from-sn (gethash from state->stateno))
                 (ct (or (aref transitions from-sn)
                         (aset transitions
                               from-sn
                               (make-char-table nil))))
                 (to (jez-nfa-tx-to tx))
                 (to-sn (gethash to state->stateno)))
            (jez-nfa-map-via-ranges (jez-nfa-tx-via tx)
              (lambda (r)
                (set-char-table-range ct r to-sn)))))))
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

(defun jez-lex-ruleset-create (productions)
  "Build a lexeer rule set.
PRODUCTIONS is a list of productions of the form

  (TOKEN PATTERN)

where TOKEN is a symbol naming the production and PATTERN is
valid input to `jez-nfa-build'.  `jex-lex-create' accepts a rule
set to build a lexer.  Return a `jez-lexer-ruleset' instance."



  )

(defun jez-lex-ruleset-goal (ruleset erx)
  "Make a lexer control pattern.
RULESET is a `jez-lex-ruleset' instance; ERX is a pattern
expression." )

(defun jez-lex-create (ruleset &key goal)
  "Build a lexer.
RULESET is a set of rules compiled with `jez-lex-create-ruleset'.
GOAL if non-`nil' is a special DFA over the rules.  Return a
`jez-lexer' instance." )

(cl-defstruct jez-lexer ())

(cl-defun jez-lex-create (rules)
  "Build a lexer.

`jez-lex-create' creates a conventional lexer.  The lexer scans
input from left to right and turns it into a token stream by
matching the input against a set of patterns.  At each point, we
simultaneously try all active patterns and use the one with the
longest match.

RULES is a list of matching rules and pragmas.  Pragma forms are
lists beginning with keyword symbols and are described below.  Non-pragma
forms are productions of the form

  (TOKEN PATTERN)

where TOKEN is a symbol naming the terminal matched.  PATTERN is
either a `jez-nfa' instance, a sexp valid as input to
`jez-nfa-build', or a string in Emacs regular expression
syntax[1].

Order of rules is significant.  When more than one rule produces
the longest match, the rule listed earlier has priority.

The following pragmas are supported:

  (:goal PATTERN)

By default, the lexer attempts to match any token at any
position.  :goal substitutes a pattern _over the tokens_ for this
match-anything rule.

:goal substitutes for the \"start conditions\" facility that
other lexer generators support.  :goal effectively automates the
generation of start conditions.

1: The pcre2el library is required for string regular expression
support.
"
  (let ((start-conditions '((INITIAL 0 nil)))
        (nr-sc 1))
    ;; Extract pragmas.  Build list of start conditions.
    (dolist (rule rules)
      (unless (consp rule)
        (error "invalid rule %S" rule))
      (cond ((eq (car rule) :start-condition)
             (cl-destructuring-bind (_ name &key exclusive) rule
               (unless (and name (not eq name t) (symbolp name))
                 (error "Start condition %S is not valid" name))
               (when (assq name start-conditions)
                 (error "Start condition %S already defined" name))
               (push (list name nr-sc exclusive) start-conditions)
               (incf nr-sc)))
            ((keywordp (car rule))
             (error "unknown rule pragma %S" rule))))
    (let* (sc-rules (make-vector nr-sc nil))
      ;; Extract rules.  For each start condition, group all the rules
      ;; that can match.
      (dolist (rule rules)
        (unless ((keywordp (car rule)))
          (cl-destructuring-bind (pattern token &key start goto)
              rule
            (let ((r2 (list pattern token goto)))
              (if (or (eq start t) (null start))
                  (dolist (sc start-conditions)
                    (let ((sc-exclusive (nth 2 sc)))
                      (when (or (eq start t) (not sc-exclusive))
                        (push r2 (aref sc-rules (nth 1 sc))))))
                (dolist (explicit-start
                          (if (symbolp start) (list start) start))
                  (let ((sc (or (car (assq explicit-start
                                           start-conditions))
                                (error "unknown start condition %S"
                                       explicit-start))))
                    (push r2 (aref sc-rules (nth 1 sc))))))))))
      ;; Now that rules are collected into the appropriate buckets, we
      ;; can build an NFA for each start state.

      )))

(defun jez-lex-configure ()
  "Set up automatic incremental lexing for the current buffer."

  )

(provide 'jezebel-lex)
