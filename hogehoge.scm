;;;;; SQL を lisp にしたい

(use gauche.collection)


;;; an example lisp database
; TODO: separate interaface from implementation

;tuple = assoc list
(define tuple0
  '((name . "kame") (age . 3)))
(define tuple1
  '((name . "kuro") (age . 5)))

;table = list of tuples
(define table0
  (list tuple0 tuple1))

; (select where table)
(define select filter)

(define (select-all table)
  (define match-all (lambda (x) #t))
  (select match-all table))

; (select-all table0)
; => (((name . "kame") (age . 3)) ((name . "kuro") (age . 5)))



(define (where= symb value)
  (lambda (tuple)
	(= (cdr (assoc 'age tuple)) value)))

;(select1 table0 (where= 'age 3))
;(((name . "kame") (age . 3)))

(define (select1 table where)
  (filter where table))
