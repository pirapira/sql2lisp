;;;;; lisp interpreter
;;;;; partially translated and executed in SQL

; depends on dbd-sqlite3
; http://practical-scheme.net/wiliki/wiliki.cgi?kikuchi
; http://autogol.ath.cx/dbd-sqlite3/Gauche-dbd-sqlite3-0.1.3.tgz

(use dbi)
(use dbd.sqlite3)
(use gauche.collection)

(define (exec-sql sql)
  (let* ((conn (dbi-connect "dbi:sqlite3:db=:memory:"))
		 )
	(dbi-do conn "CREATE TABLE hoge (num int)")
	(dbi-do conn "INSERT INTO hoge VALUES (8)")
	(dbi-do conn sql)))

(define (map-equal? a b)
  (equal?
   (map values a)
   (map values b)))

(define (test-exec-sql)
  (define (test-exec-sql-inner sql)
	(map-equal? (exec-sql sql) (exec-sql sql)))
  (test-exec-sql-inner "select * from hoge"))


;(define (test sql lisp)
;  (equal? (exec-sql sql) (exec-lisp lisp)))

(define (failing-test) #f)

(define tests
  (list
   test-exec-sql
;   failing-test
   ))

(for-each
 (lambda (x) (or (x) (error 'test-failed)))
 tests)
