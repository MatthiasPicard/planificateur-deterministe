(define (domain taquin-puzzle)
  (:requirements :strips :typing)
  (:types tile cell) 
  (:predicates
    (on ?t - tile ?c - cell)
    (touch ?c1 - cell ?c2 - cell)
    (empty ?c - cell)
  )
  (:action move
    :parameters (?t - tile ?from - cell ?to - cell)
    :precondition (and (on ?t ?from) (empty ?to) (touch ?from ?to))
    :effect (and (not (on ?t ?from)) (not (empty ?to)) (on ?t ?to) (empty ?from))
  )
)
