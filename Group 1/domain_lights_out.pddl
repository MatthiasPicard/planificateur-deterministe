(define (domain lights_out)
    (:requirements :strips :typing)
    (:types light)
    (:predicates (adjacent ?l1 - light ?l2 - light)  (on ?l1 - light))
    (:action switch
        :parameters (?l1 - light)
        :precondition (or (on ?l1) (not (on ?l1)))
        :effect (and (when (on ?l1) (not (on ?l1))) (when (not (on ?l1)) (on ?l1)) (forall (?l2 - light) (when (and (adjacent ?l1 ?l2) (not (on ?l2))) (on ?l2))) (forall (?l2 - light) (when (and (adjacent ?l1 ?l2) (on ?l2)) (not (on ?l2)))))
    )
)