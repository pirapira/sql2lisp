;;;;; SQL を lisp にしたい
;(select table0 (where= 'age 3)) 的な
;しかし，なんか逆のことをしている気がしてきたので撤退．

(use gauche.collection)
(use srfi-1)

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
  (where-pred (list symb) (lambda (x) (equal? x value))))


;delete implementation
; (delete table0 (where= 'age 3))
; => (((name . "kuro") (age . 5)))
(define (delete table where)
  (filter (lambda (x) (not (where x))) table))

;insert implementation
; (insert '((name . "jiro")) table0)
; (((name . "jiro")) ((name . "kame") (age . 3)) ((name . "kuro") (age . 5)))
(define insert cons)

;update implementation
; (update table0 '((name . "taro")) (where= 'name "kuro"))
; => (((name . "kame") (age . 3))
;     ((name . "taro") (age . 5)))

(define (update table tuple where)
  (map
   (lambda (t)
	 (if (where t)
		 (update-tuple tuple t)
		 t))
   table))

(define (update-tuple new old)
  (if (null? new)
	  old
	  (let* ((head (car new))
			 (key  (car head))
			 (val  (cdr head)))
		(acons key val (alist-delete key old)))))

;;; SQL parser



;;; SQL to lisp compiler

