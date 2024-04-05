(define (problem problem_logistics)
(:domain basic_logistics)
(:requirements :strips :typing)

    (:objects 
        wp1 wp2 wp3 wp4 wp5 wp6 wp7 wp8 wp9 wp10 wp11 wp12 wp13 wp14 wp15 wp16 wp17 wp18 wp19 wp20 - location
        t1 t2 t3 - truck
        dr1 dr2 dr3 dr4 - driver
        pack1 pack2 pack3 pack4 pack5 pack6 - package
    )
    
    (:init
        ;; drivers
        (at dr1 wp11)
        (at dr2 wp12)
        (at dr3 wp13)
        (at dr4 wp16)
        
        ;; trucks
        (at t1 wp2)
        (at t2 wp10)
     	(at t3 wp14)
        
        ;; packages
        (at pack1 wp4)
        (at pack2 wp6)
        (at pack3 wp7)
        (at pack4 wp15)
     	(at pack5 wp17)
     	(at pack6 wp18)
        
        ;; Ground Connections
     	(connected wp1 wp18)
        (connected wp18 wp1)
        (connected wp1 wp6)
        (connected wp6 wp1)
        (connected wp1 wp7)
        (connected wp7 wp1)
        (connected wp2 wp12)
        (connected wp12 wp2)
        (connected wp3 wp14)
        (connected wp14 wp3)
        (connected wp3 wp17)
        (connected wp17 wp3)
        (connected wp3 wp8)
        (connected wp8 wp3)
        (connected wp3 wp13)
        (connected wp13 wp3)
        (connected wp3 wp16)
        (connected wp16 wp3)
        (connected wp3 wp20)
        (connected wp20 wp3)
        (connected wp4 wp20)
        (connected wp20 wp4)
        (connected wp4 wp18)
        (connected wp18 wp4)
        (connected wp4 wp7)
        (connected wp7 wp4)
        (connected wp5 wp12)
        (connected wp12 wp5)
        (connected wp5 wp14)
        (connected wp14 wp5)
        (connected wp6 wp11)
        (connected wp11 wp6)
        (connected wp7 wp18)
        (connected wp18 wp7)
        (connected wp7 wp12)
        (connected wp12 wp7)
        (connected wp7 wp16)
        (connected wp16 wp7)
        (connected wp8 wp19)
        (connected wp19 wp8)
        (connected wp9 wp13)
        (connected wp13 wp9)
        (connected wp10 wp19)
        (connected wp19 wp10)
        (connected wp10 wp18)
        (connected wp18 wp10)
        (connected wp14 wp15)
        (connected wp15 wp14)
        (connected wp16 wp19)
        (connected wp19 wp16)
        (connected wp17 wp20)
        (connected wp20 wp17)
        (connected wp19 wp20)
        (connected wp20 wp19)
    )
    
    (:goal (and 
        ;; drivers home
        (at dr1 wp11)
        (at dr2 wp12)
        (at dr3 wp13)
        (at dr4 wp16)
        ;; trucks at their initial location

        ;; packages delivered
        (at pack1 wp4)
        (at pack2 wp8)
        (at pack3 wp11)
        (at pack4 wp14)
     	(at pack5 wp7)
     	(at pack6 wp2)
    ))
)