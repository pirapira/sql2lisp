;;; test codes for relation library of Gauche

(use util.relation)

;;; how to create a relation?

(define rel (make <simple-relation>))
(relation-rows rel) ; -> ()
(relation-column-names rel)	; -> ()
(slot-ref rel 'columns)		; -> ()
(relation-insertable? rel)	; -> #t		always #t for simple-relation
(slot-set! rel 'columns '(name address phone))
(slot-ref rel 'columns)		; -> (name address phone)
(relation-insert! rel '("yh" "jimbocho" "N/A"))
(slot-ref rel 'rows)		; -> (("yh" "jimbocho" "N/A"))

;;; future usage
; (join rel0 rel1)
; (group-by rel)
