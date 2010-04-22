;;;;; lisp interpreter
;;;;; partially translated and executed in SQL

; depends on dbd-sqlite3
; http://practical-scheme.net/wiliki/wiliki.cgi?kikuchi
; http://autogol.ath.cx/dbd-sqlite3/Gauche-dbd-sqlite3-0.1.3.tgz

(use dbi)
(use dbd.sqlite3)
(use gauche.collection)

(define (create-db)
  (let ((conn (dbi-connect "dbi:sqlite3:db=:memory:"))
		 )
	(dbi-do conn "CREATE TABLE mail (num int)")
	(dbi-do conn "INSERT INTO hoge VALUES (8)")
	conn))

(define (exec-sql sql)
  (let ((conn (create-db)))
	(dbi-do conn sql)))

(define (exec-lisp lisp)
	(eval 
	 `(let ((conn (create-db))
			(hoge
			 (lambda ()
			   (map values (dbi-do conn "SELECT * from hoge"))))
			)
		,lisp)
	 (interaction-environment)))

(define (map-equal? a b)
  (equal?
   (map values a)
   (map values b)))


;; a test to succeed
(define (test-exec-sql)
  (define (test-exec-sql-inner sql)
	(map-equal? (exec-sql sql) (exec-sql sql)))
  (test-exec-sql-inner "select * from hoge"))

;; a test to fail
(define (failing-test) #f)

;; the main tests
(define (compare-sql-lisp sql lisp)
  (map-equal? (exec-sql sql) (exec-lisp lisp)))

(define (sql-lisp-simplest-test)
  (compare-sql-lisp
   "select * from hoge"
   '(hoge)))

(define tests
  (list
   test-exec-sql
   sql-lisp-simplest-test
;   failing-test
   ))

(define (test)
  (for-each
   (lambda (x) (or (x) (error 'test-failed)))
   tests))

(test)

