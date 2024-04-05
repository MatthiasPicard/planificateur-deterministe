(define
(problem test)
(:domain rubiks-cube)
(:objects yellow white blue green orange red)
(:init
    (cube1 orange blue white)
    (cube2 red blue white)
    (cube3 red white green)
    (cube4 red blue yellow)
    (cube5 green yellow red)
    (cube6 green orange white)
    (cube7 orange yellow blue)
    (cube8 yellow green orange)
)
(:goal
    (and
        (cube1 red white blue)
        (cube2 orange white blue)
        (cube3 red yellow blue)
        (cube4 orange yellow blue)
        (cube5 red white green)
        (cube6 orange white green)
        (cube7 red yellow green)
        (cube8 orange yellow green)

    )
)
)