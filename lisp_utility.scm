(define (group-by eq ungrouped)
  (if (null? ungrouped) '()
	  (receive ((split rest (span (lambda (x) (eq x (car ungrouped))) ungrouped)))
		(cons split (group-by eq rest)))))

