(define (domain maze)
  (:requirements :strips)
  (:types agent position)
  (:predicates 
    (inc ?a ?b - position)
    (dec ?a ?b - position)
    (can_jump ?a - agent)
    (at ?a - agent ?x ?y - position)
    (wall ?x ?y)
    )
   
   (:action 
    jump-right
    :parameters (?omf - agent)
    :precondition (can_jump ?omf)
    :effect (forall (?x ?y ?yn - position)
                    (when 
                      (and (at ?omf ?x ?y)
                            (inc ?x ?xn)
                           (wall ?x ?yn))
                      (and (not (at ?omf ?x ?y))
                           (at ?omf ?x ?yn)
                           (not(can_jump ?omf)))
                      )
                    )
    ) 
    
    
   (:action 
    jump-left
    :parameters (?omf - agent)
    :precondition (can_jump ?omf)
    :effect (forall (?x ?y ?yn - position)
                    (when 
                      (and (at ?omf ?x ?y)
                            (dec ?x ?xn)
                           (wall ?x ?yn))
                      (and (not (at ?omf ?x ?y))
                           (at ?omf ?x ?yn)
                           (not(can_jump ?omf)))
                      )
                    )
    ) 
    
   (:action 
    jump-down
    :parameters (?omf - agent)
    :precondition (can_jump ?omf)
    :effect (forall (?x ?y ?yn - position)
                    (when 
                      (and (at ?omf ?x ?y)
                            (inc ?y ?yn)
                           (wall ?x ?yn))
                      (and (not (at ?omf ?x ?y))
                           (at ?omf ?x ?yn)
                           (not(can_jump ?omf)))
                      )
                    )
    ) 
    
   (:action 
    jump-up
    :parameters (?omf - agent)
    :precondition (can_jump ?omf)
    :effect (forall (?x ?y ?yn - position)
                    (when 
                      (and (at ?omf ?x ?y)
                           (dec ?y ?yn)
                           (wall ?x ?yn))
                      (and (not (at ?omf ?x ?y))
                           (at ?omf ?x ?yn)
                           (not(can_jump ?omf)))
                      )
                    )
    ) 
   
   
  (:action 
    move-up
    :parameters (?omf - agent)
    :precondition ()
    :effect (forall (?x ?y ?yn - position)
                    (when 
                      (and (at ?omf ?x ?y)
                           (dec ?y ?yn)
                           (not (wall ?x ?yn)))
                      (and (not (at ?omf ?x ?y))
                           (at ?omf ?x ?yn))
                      )
                    )
    )

  (:action 
    move-down
    :parameters (?omf - agent)
    :precondition ()
    :effect (forall (?x ?y ?yn - position)
                    (when 
                      (and (at ?omf ?x ?y)
                           (inc ?y ?yn)
                           (not (wall ?x ?yn)))
                      (and (not (at ?omf ?x ?y))
                           (at ?omf ?x ?yn))
                      )
                    )
    )

  (:action 
    move-right
    :parameters (?omf - agent)
    :precondition ()
    :effect (forall (?x ?y ?xn - position)
                    (when 
                      (and (at ?omf ?x ?y)
                           (inc ?x ?xn)
                           (not (wall ?xn ?y)))
                      (and (not (at ?omf ?x ?y))
                           (at ?omf ?xn ?y))
                      )
                    )
    )

  (:action 
    move-left
    :parameters (?omf - agent)
    :precondition ()
    :effect (forall (?x ?y ?xn - position)
                    (when 
                      (and (at ?omf ?x ?y)
                           (dec ?x ?xn)
                           (not (wall ?xn ?y)))
                      (and (not (at ?omf ?x ?y))
                           (at ?omf ?xn ?y))
                      )
                    )
    )
  )