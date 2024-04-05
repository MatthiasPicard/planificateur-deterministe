(define (problem taquin-size3x3-number_4)
  (:domain taquin-puzzle)
  (:objects
    tile_0 - tile
    tile_1 - tile
    tile_2 - tile
    tile_3 - tile
    tile_4 - tile
    tile_5 - tile
    tile_6 - tile
    tile_7 - tile
    cell_0 - cell
    cell_1 - cell
    cell_2 - cell
    cell_3 - cell
    cell_4 - cell
    cell_5 - cell
    cell_6 - cell
    cell_7 - cell
    cell_8 - cell
  )
  (:init
    (touch cell_0 cell_3)
    (touch cell_0 cell_1)
    (touch cell_1 cell_4)
    (touch cell_1 cell_0)
    (touch cell_1 cell_2)
    (touch cell_2 cell_5)
    (touch cell_2 cell_1)
    (touch cell_3 cell_0)
    (touch cell_3 cell_6)
    (touch cell_3 cell_4)
    (touch cell_4 cell_1)
    (touch cell_4 cell_7)
    (touch cell_4 cell_3)
    (touch cell_4 cell_5)
    (touch cell_5 cell_2)
    (touch cell_5 cell_8)
    (touch cell_5 cell_4)
    (touch cell_6 cell_3)
    (touch cell_6 cell_7)
    (touch cell_7 cell_4)
    (touch cell_7 cell_6)
    (touch cell_7 cell_8)
    (touch cell_8 cell_5)
    (touch cell_8 cell_7)
    (on tile_4 cell_0)
    (on tile_0 cell_1)
    (on tile_2 cell_2)
    (on tile_5 cell_3)
    (on tile_3 cell_4)
    (on tile_7 cell_5)
    (on tile_1 cell_6)
    (on tile_6 cell_7)
    (empty cell_8)
  )
  (:goal (and
    (on tile_0 cell_0)
    (on tile_1 cell_1)
    (on tile_2 cell_2)
    (on tile_3 cell_3)
    (on tile_4 cell_4)
    (on tile_5 cell_5)
    (on tile_6 cell_6)
    (on tile_7 cell_7)
  ))
)
