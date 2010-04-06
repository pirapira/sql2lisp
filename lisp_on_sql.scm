;;;;; lisp execution on RDBMS.
;;;;; storing values for variables in a database management system!

(define (exec-sql sql)
  (display sql))

(define (eval-atom-on-db atom)
  (exec-sql (format "SELECT FROM env WHERE symb = ~a" atom)))

(define (eval-on-db term)
  (cond ((equal? (car term) 'define)
		 (exec-sql (format "INSERT INTO env VALUES (~a, ~a)"
						   (cadr term) (caddr term))))
		(#t (error 'unimplemented))))
