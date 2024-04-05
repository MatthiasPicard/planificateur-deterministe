(define (problem nonogram_2x2_conf1)
  (:domain nonogram)
  (:objects
    cell00 cell01 - cell
    cell10 cell11 - cell
    row1 row2 - row
    col1 col2 - col
  )

  (:init
    (empty cell00) (empty cell01)
    (empty cell10) (empty cell11)
    (adjacent cell00 cell01) ; Specify adjacent cells in the initial state
    (adjacent cell10 cell11)
    (in-col cell00 col1) ; Specify column positions in the initial state
    (in-col cell01 col2)
    (in-col cell10 col1)
    (in-col cell11 col2)
    (in-row cell00 row1) ; Specify row positions in the initial state
    (in-row cell01 row1)
    (in-row cell10 row2)
    (in-row cell11 row2)
  )

  (:goal
    (and
      ; Column 1 should have 2 adjacent cells colored
      (exists (?cell1 ?cell2)
        (and
          (filled ?cell1) (filled ?cell2)           ; Two cells in column 1
          (in-col ?cell1 col1) (in-col ?cell2 col1) ; Both cells in column 1
          (adjacent ?cell1 ?cell2)           ; They should be adjacent
        )
      )

      ; One cell colored in column 2, and its adjacent cell in the same line is marked
      (exists (?cell ?adj-cell)
        (and
          (filled ?cell) (in-col ?cell col2)         ; Cell is filled and in column 2
          (adjacent ?cell ?adj-cell)          ; They should be adjacent
          (in-col ?cell ?col) (in-col ?adj-cell ?col) ; Both cells are in the same column
          (marked ?adj-cell)                        ; Adjacent cell is marked
        )
      )


      ; One cell colored in line 1, and its adjacent cells on the same line are marked
      (exists (?cell ?adj-cell)
        (and
          (filled ?cell) (in-col ?cell row1)         ; Cell is filled and in row 1
          (adjacent ?cell ?adj-cell)          ; They should be adjacent
          (in-row ?cell ?row) (in-row ?adj-cell ?row) ; Both cells are in the same row
          (marked ?adj-cell)                        ; Adjacent cell is marked
        )
      )


      ; Two cells colored in line 2
      (exists (?cell1 ?cell2)
        (and
          (filled ?cell1) (filled ?cell2)           ; Two cells in row 2
          (in-row ?cell1 row2) (in-col ?cell2 row2) ; Both cells in row 2
          (adjacent ?cell1 ?cell2)           ; They should be adjacent
        )
      )
    )
  )
)
