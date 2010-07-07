;;;;; lisp interpreter
;;;;; partially translated and executed in SQL

; depends on dbd-sqlite3
; http://practical-scheme.net/wiliki/wiliki.cgi?kikuchi
; http://autogol.ath.cx/dbd-sqlite3/Gauche-dbd-sqlite3-0.1.3.tgz


;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; intermediate language ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
;; Syntax
; (('filter f0 f1 ... fn)
;  ('sorter s0 s1 ... sn))
; where f0, ..., fn are closures that take a row and return #t or #f.
;       s0, ..., sn are row names (symbol or string <- to be determined).
;
;; Scheme meaning
; (lambda (x) (sort ... (sort (sort (filter f0 (filter f1 ... (filter fn x))) <s0>) <s1>) ... <sn>) x)
; where <s> is a comparator 
;
;; SQL meaning
; WHERE [f0] AND [f1] AND [f2] ORDER BY sn, ..., s1, s0
;
;
;; Remark
; For f0, ... fn, the order is irrelevant to the results.
; For s0, ... sn, the order is relevant to the results.
; 

(use util.relation)

(define (assert b)
  (unless b (error 'assert-failure)))

;; <s> implimentation
(define (cmp-on-column s r)
  ; s: column name
  ; r: relation
  (assert (member s (relation-column-names r)))
  (let ((acc (lambda (row) ((relation-accessor r) s row))))
    (lambda (row0 row1) (< (acc row0) (acc row1)))))

;; [f] implimentation
; predicate transformer from S-exp to SQL
; more difficult because it involves parsing.

; input (lambda (row) (equal? 3 ((relation-accessor r) s row)))
; output S = 3

; input (lambda (row) (rxmatch (string->regexp "^hs*") ((relation-accessor r) s row)))
; output S IS LIKE "hs%"

