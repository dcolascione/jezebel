;; -*- lexical-binding: t -*-
;; Fully incremental GLR parser for Jezebel editing environments.
;; Based on the IGLR algorithm in Tim A. Wagner's "Practical
;; Algorithms for Incremental Software Development Environments"

(require 'jezebel-util)
(require 'jezebel-lr)

(cl-defstruct jez-iglr-node
   ;; production or symbol #
  type
  ;; deterministic parse state or noState
  state
  ;; setof NODE kids: rhs of a production; interpretations of a symbol
  kids)

(cl-defstruct (jez-iglr-symbol (:include jez-iglr-node))
  )

(cl-defstruct jez-iglr-gss-node
  ;; state of constructing parser
  state
  ;; setof LINK links; links to earlier nodes
  links)

(cl-defstruct jez-iglr-gss-link
  ;; preceding node in the GSS
  head
  ;; parse dag node labeling this edge
  node)

(cl-defstruct jez-iglr-state
  ;; bool multipleStates
  multiple-states

  ;; lookahead symbol (subtree)
  shift-la

  ;; lookahead for reducing
  red-la

  ;; GSS_NODE acceptingParser
  accepting-parser

  active-parsers
  for-actor
  for-shifter

  ;; production node merge table
  nodes

  ;; symbol node merge table
  symbol-nodes

  ;; parse-table
  parse-table)

(defun jez-iglr-parse-incremental (iglr root)
  (jez-iglr-process-modifications-to-parse-dag root)
  
  )



(provide 'jezebel-iglr)
