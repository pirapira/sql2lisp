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
	(dbi-do conn "CREATE TABLE mail (num int, from_addr string)")
	(dbi-do conn "INSERT INTO mail VALUES (8, 'john@example.com')")
	(dbi-do conn "INSERT INTO mail VALUES (8, 'bob@example.com')")
	conn))

(define (exec-sql sql)
  (let ((conn (create-db)))
	(dbi-do conn sql)))

(define (exec-lisp lisp)
	(eval 
	 `(let* ((conn (create-db))
			(mail
			 (lambda ()
			   (map values (dbi-do conn "SELECT * from mail"))))
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
  (test-exec-sql-inner "select * from mail"))

;; a test to fail
(define (failing-test) #f)

;; the main tests
(define (compare-sql-lisp sql lisp)
  (map-equal? (exec-sql sql) (exec-lisp lisp)))

(define (sql-lisp-simplest-test)
  (compare-sql-lisp
   "select * from mail"
   '(mail)))

;; excersize problems
(define (ex->test ex)
  (lambda () (compare-sql-lisp (cdr ex) (car ex))))

(load "./samples")

(define tests
  (list
   test-exec-sql
   sql-lisp-simplest-test
;   failing-test ;uncomment this line to see error.
   (ex->test ex1)
;   (ex->test ex2)
;   (ex->test ex3)
;   (ex->test ex5)
   ))

(define (test)
  (for-each
   (lambda (x) (or (x) (error 'test-failed)))
   tests))

(test)

