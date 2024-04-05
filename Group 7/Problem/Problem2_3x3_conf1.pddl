(define (problem nonogram_3x3_conf1)
  (:domain nonogram)
  (:objects
    cell00 cell01 cell02 - cell
    cell10 cell11 cell12 - cell
    cell20 cell21 cell22 - cell
    row1 row2 row3 - row
    col1 col2 col3 - col
  )

  (:init
    (empty cell00) (empty cell01) (empty cell02)
    (empty cell10) (empty cell11) (empty cell12)
    (empty cell20) (empty cell21) (empty cell22)
    (adjacent cell00 cell01) ; Specify adjacent cells in the initial state
    (adjacent cell01 cell02)
    (adjacent cell10 cell11)
    (adjacent cell11 cell12)
    (adjacent cell20 cell21)
    (adjacent cell21 cell22)
    (adjacent cell00 cell10)
    (adjacent cell10 cell20)
    (adjacent cell01 cell11)
    (adjacent cell11 cell21)
    (adjacent cell02 cell12)
    (adjacent cell12 cell22)
    (in-col cell00 col1) ; Specify column positions in the initial state
    (in-col cell01 col2)
    (in-col cell02 col3)
    (in-col cell10 col1)
    (in-col cell11 col2)
    (in-col cell12 col3)
    (in-col cell20 col1)
    (in-col cell21 col2)
    (in-col cell22 col3)
    (in-row cell00 row1) ; Specify row positions in the initial state
    (in-row cell01 row1)
    (in-row cell02 row1)
    (in-row cell10 row2)
    (in-row cell11 row2)
    (in-row cell12 row2)
    (in-row cell20 row3)
    (in-row cell21 row3)
    (in-row cell22 row3)
  )

  (:goal
    (and
      ; Column 1 should have 3 adjacent cells colored
      (exists (?cell1 ?cell2 ?cell3)
        (and
          (filled ?cell1) (filled ?cell2) (filled ?cell3)
          (in-col ?cell1 col1) (in-col ?cell2 col1) (in-col ?cell3 col1)
          (adjacent ?cell1 ?cell2) (adjacent ?cell2 ?cell3)
        )
      )

      ; One cell colored in column 2, and its adjacent cells in the same line marked
      (exists (?cell1 ?cell2 ?cell3)
        (and
          (filled ?cell1) (marked ?cell2) (marked ?cell3)
          (in-col ?cell1 col2) (in-col ?cell2 col2) (in-col ?cell3 col2)
        )
      )

      ; One cell colored in column 3, and its adjacent cells in the same line marked
      (exists (?cell1 ?cell2 ?cell3)
        (and
          (filled ?cell1) (marked ?cell2) (marked ?cell3)
          (in-col ?cell1 col3) (in-col ?cell2 col3) (in-col ?cell3 col3)
        )
      )


      ; One cell colored in line 1, and its adjacent cells on the same line are marked
      (exists (?cell1 ?cell2 ?cell3)
        (and
          (filled ?cell1) (marked ?cell2) (marked ?cell3)
          (in-row ?cell1 row1) (in-row ?cell2 row1) (in-row ?cell3 row1)
        )
      )


      ; Two cells colored in line 2
      (exists (?cell1 ?cell2 ?cell3)
        (and
          (filled ?cell1) (filled ?cell2) (marked ?cell3)
          (in-row ?cell1 row2) (in-row ?cell2 row2) (in-row ?cell3 row2)
          (adjacent ?cell1 ?cell2)
        )
      )

      ; Two non adjacent cells colored in line 3
      (exists (?cell1 ?cell2 ?cell3)
        (and
          (filled ?cell1) (filled ?cell2) (marked ?cell3)
          (in-row ?cell1 row3) (in-row ?cell2 row3) (in-row ?cell3 row3)
          (not(adjacent ?cell1 ?cell2))
        )
      )
    )
  )
)
