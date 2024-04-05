(define (problem taquin-size2x2-number_0)
  (:domain taquin-puzzle)
  (:objects
    tile_0 - tile
    tile_1 - tile
    tile_2 - tile
    cell_0 - cell
    cell_1 - cell
    cell_2 - cell
    cell_3 - cell
  )
  (:init
    (touch cell_0 cell_2)
    (touch cell_0 cell_1)
    (touch cell_1 cell_3)
    (touch cell_1 cell_0)
    (touch cell_2 cell_0)
    (touch cell_2 cell_3)
    (touch cell_3 cell_1)
    (touch cell_3 cell_2)
    (on tile_1 cell_0)
    (on tile_2 cell_1)
    (on tile_0 cell_2)
    (empty cell_3)
  )
  (:goal (and
    (on tile_0 cell_0)
    (on tile_1 cell_1)
    (on tile_2 cell_2)
  ))
)
