(define (domain tsp)
  (:requirements :strips)
  (:predicates  (in ?x) 
                (delivered ?x)
	            (connected ?x ?y))

  (:action go_to
    :parameters     (?x ?y)
    :precondition   (and (in ?x)
		            (connected ?x ?y))
    :effect         (and (not (in ?x))
                    (in ?y) ))

  (:action deliver
    :parameters     (?x)
    :precondition   (and (in ?x) 
                    (not (delivered ?x)))

    :effect         (delivered ?x )))