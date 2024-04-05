(define
(problem test)
(:domain rubiks-cube)
(:objects yellow white blue green orange red)
(:init
    (cube1 blue orange yellow)
    (cube2 green yellow red)
    (cube3 white orange green)
    (cube4 orange blue white)
    (cube5 blue white red)
    (cube6 white red green)
    (cube7 red blue yellow)
    (cube8 orange yellow green)
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