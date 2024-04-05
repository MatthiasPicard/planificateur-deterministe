(define (domain nonogram)
  (:requirements :strips :typing)
  (:types cell row col)
  (:predicates
    (filled ?cell - cell)
    (empty ?cell - cell)
    (marked ?cell - cell)
    (adjacent ?cell1 - cell ?cell2 - cell)
    (in-row ?cell - cell ?row - row)
    (in-col ?cell - cell ?col - col)
  )
  
  (:action fill
    :parameters (?cell - cell)
    :precondition (empty ?cell)
    :effect (filled ?cell)
  )

  (:action mark
    :parameters (?cell - cell)
    :precondition (empty ?cell)
    :effect (marked ?cell)
  )

)
