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

;select implementation
(define (select table where)
  (filter where table))

;general where clause
;n-ary condition and n-symbols
(define (where-pred symbs condition)
  (lambda (tuple)
	(apply condition
	 (map
	  (lambda (symb)
		(cdr (assoc symb tuple)))
	  symbs))))

;equality condition
; (select table0 (where= 'age 3))
; => (((name . "kame") (age . 3)))
(define (where= symb value)
  (where-pred (list symb) (lambda (x) (= x value))))

