(define (problem problem_logistics)
(:domain basic_logistics)
(:requirements :strips :typing)

    (:objects 
        wp1 wp2 wp3 wp4 wp5 wp6 wp7 wp8 wp9 wp10 wp11 - location
        t1 t2 - truck
        dr1 dr2 - driver
        pack1 pack2 pack3 pack4 - package
    )
    
    (:init
        ;; drivers
        (at dr1 wp4)
        (at dr2 wp1)
        
        ;; trucks
        (at t1 wp6)
        (at t2 wp9)
        
        ;; packages
        (at pack1 wp2)
        (at pack2 wp3)
        (at pack3 wp5)
        (at pack4 wp11)
        
        ;; Ground Connections
        (connected wp1 wp2)
        (connected wp2 wp1)
        (connected wp1 wp4)
        (connected wp4 wp1)
        (connected wp2 wp4)
        (connected wp4 wp2)
        (connected wp2 wp5)
        (connected wp5 wp2)
        (connected wp2 wp7)
        (connected wp7 wp2)
        (connected wp3 wp6)
        (connected wp6 wp3)
        (connected wp4 wp13)
        (connected wp13 wp4)
        (connected wp4 wp11)
        (connected wp11 wp4)
        (connected wp5 wp10)
        (connected wp10 wp5)
        (connected wp6 wp10)
        (connected wp10 wp6)
        (connected wp6 wp9)
        (connected wp9 wp6)
        (connected wp8 wp9)
        (connected wp9 wp8)
        (connected wp8 wp10)
        (connected wp10 wp8)
        (connected wp10 wp12)
        (connected wp12 wp10)
        (connected wp10 wp13)
        (connected wp13 wp10)
    )
    
    (:goal (and 
        ;; drivers home
        (at dr1 wp1)
        (at dr2 wp1)
        
        ;; packages delivered
        (at pack1 wp9)
        (at pack2 wp2)
        (at pack3 wp9)
        (at pack4 wp2)
    ))
)