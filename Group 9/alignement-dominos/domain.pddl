(define (domain alignement-dominos)
  (:requirements :strips :typing :equality)
  
  (:types domino number)
  
  (:predicates
    (TableVide)
    (EnMain ?d - domino)
    (ChiffreGauche ?c - number ?d - domino)
    (ChiffreDroit ?c - number ?d - domino)
    (LibreGauche ?c - number)
    (LibreDroit ?c - number)
  )
  
  (:action TournerDomino
    :parameters (?d - domino ?cg - number ?cd - number)
    :precondition (and (EnMain ?d) 
                       (ChiffreGauche ?cg ?d) 
                       (ChiffreDroit ?cd ?d))
    :effect (and (ChiffreGauche ?cd ?d) 
                 (ChiffreDroit ?cg ?d) 
                 (when (not (= ?cg ?cd))
                    (and 
                        (not (ChiffreGauche ?cg ?d)) 
                        (not (ChiffreDroit ?cd ?d)))
                 ))
  )
  
  (:action PoserLibre
    :parameters (?d - domino ?cg - number ?cd - number)
    :precondition (and (EnMain ?d) 
                       (ChiffreGauche ?cg ?d) 
                       (ChiffreDroit ?cd ?d) 
                       (TableVide))
    :effect (and (not (EnMain ?d)) 
                 (not (TableVide)) 
                 (LibreGauche ?cg) 
                 (LibreDroit ?cd))
  )
  
  (:action PoserGauche
    :parameters (?d - domino ?cg - number ?cd - number)
    :precondition (and (EnMain ?d) 
                       (ChiffreGauche ?cg ?d) 
                       (ChiffreDroit ?cd ?d) 
                       (LibreGauche ?cd))
    :effect (and 
                (not (EnMain ?d)) 
                (when (not (= ?cg ?cd))
                    (and (not (LibreGauche ?cd))
                         (LibreGauche ?cg)
                    )
                )
            )
                         
  )
  
  (:action PoserDroit
    :parameters (?d - domino ?cg - number ?cd - number)
    :precondition (and (EnMain ?d) 
                       (ChiffreGauche ?cg ?d) 
                       (ChiffreDroit ?cd ?d) 
                       (LibreDroit ?cg))
    :effect (and (not (EnMain ?d)) 
                (when (not (= ?cg ?cd))
                    (and (not (LibreDroit ?cg))
                         (LibreDroit ?cd)
                    )
                )
            )
  )
)