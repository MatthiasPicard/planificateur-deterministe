(define (problem nonogram_4x4_conf1)
  (:domain nonogram)
  (:objects
    cell00 cell01 cell02 cell03 - cell
    cell10 cell11 cell12 cell13 - cell
    cell20 cell21 cell22 cell23 - cell
    cell30 cell31 cell32 cell33 - cell
    row1 row2 row3 row4 - row
    col1 col2 col3 col4 - col
  )

  (:init
    (empty cell00) (empty cell01) (empty cell02) (empty cell03)
    (empty cell10) (empty cell11) (empty cell12) (empty cell13)
    (empty cell20) (empty cell21) (empty cell22) (empty cell23)
    (empty cell30) (empty cell31) (empty cell32) (empty cell33)
    (adjacent cell00 cell01) ; Specify adjacent cells in the initial state
    (adjacent cell01 cell02)
    (adjacent cell02 cell03)
    (adjacent cell10 cell11)
    (adjacent cell11 cell12)
    (adjacent cell12 cell13)
    (adjacent cell20 cell21)
    (adjacent cell21 cell22)
    (adjacent cell22 cell23)
    (adjacent cell30 cell31)
    (adjacent cell31 cell32)
    (adjacent cell32 cell33)

    (adjacent cell00 cell10)
    (adjacent cell10 cell20)
    (adjacent cell20 cell30)
    (adjacent cell01 cell11)
    (adjacent cell11 cell21)
    (adjacent cell21 cell31)
    (adjacent cell02 cell12)
    (adjacent cell12 cell22)
    (adjacent cell22 cell32)
    (adjacent cell03 cell13)
    (adjacent cell13 cell23)
    (adjacent cell23 cell33)
    (in-col cell00 col1) ; Specify column positions in the initial state
    (in-col cell01 col2)
    (in-col cell02 col3)
    (in-col cell03 col4)
    (in-col cell10 col1)
    (in-col cell11 col2)
    (in-col cell12 col3)
    (in-col cell13 col4)
    (in-col cell20 col1)
    (in-col cell21 col2)
    (in-col cell22 col3)
    (in-col cell23 col4)
    (in-col cell30 col1)
    (in-col cell31 col2)
    (in-col cell32 col3)
    (in-col cell33 col4)
    (in-row cell00 row1) ; Specify row positions in the initial state
    (in-row cell01 row1)
    (in-row cell02 row1)
    (in-row cell03 row1)
    (in-row cell10 row2)
    (in-row cell11 row2)
    (in-row cell12 row2)
    (in-row cell13 row2)
    (in-row cell20 row3)
    (in-row cell21 row3)
    (in-row cell22 row3)
    (in-row cell23 row3)
    (in-row cell30 row4)
    (in-row cell31 row4)
    (in-row cell32 row4)
    (in-row cell33 row4)
  )

  (:goal
    (and
      ; Column 1 should have 2 adjacent cells colored
      (exists (?cell1 ?cell2 ?cell3 ?cell4)
        (and
          (filled ?cell1) (filled ?cell2) (marked ?cell3) (marked ?cell4)
          (in-col ?cell1 col1) (in-col ?cell2 col1) (in-col ?cell3 col1) (in-col ?cell4 col1)
          (adjacent ?cell1 ?cell2)
        )
      )

      ; Column 2 should have 4 adjacent cells colored
      (exists (?cell1 ?cell2 ?cell3 ?cell4)
        (and
          (filled ?cell1) (filled ?cell2) (filled ?cell3) (filled ?cell4)
          (in-col ?cell1 col2) (in-col ?cell2 col2) (in-col ?cell3 col2) (in-col ?cell4 col2)
          (adjacent ?cell1 ?cell2) (adjacent ?cell2 ?cell3) (adjacent ?cell3 ?cell4)
        )
      )

      ; Two non adjacent cells colored in column 3
      (exists (?cell1 ?cell2 ?cell3 ?cell4)
        (and
          (filled ?cell1) (filled ?cell2) (marked ?cell3) (marked ?cell4)
          (in-col ?cell1 col3) (in-col ?cell2 col3) (in-col ?cell3 col3) (in-col ?cell4 col3)
          (not (adjacent ?cell1 ?cell2))
        )
      )

      ; 1 then 2 in column 4
      (exists (?cell1 ?cell2 ?cell3 ?cell4)
        (and
          (filled ?cell1) (filled ?cell2) (filled ?cell3) (marked ?cell4)
          (in-col ?cell1 col3) (in-col ?cell2 col3) (in-col ?cell3 col3) (in-col ?cell4 col3)
          (not (adjacent ?cell1 ?cell2)) (not (adjacent ?cell1 ?cell3)) (adjacent ?cell2 ?cell3)
        )
      )

      ; row 1 should have 3 adjacent cells colored
      (exists (?cell1 ?cell2 ?cell3 ?cell4)
        (and
          (filled ?cell1) (filled ?cell2) (filled ?cell3) (marked ?cell4)
          (in-row ?cell1 row1) (in-row ?cell2 row1) (in-row ?cell3 row1) (in-row ?cell4 row1)
          (adjacent ?cell1 ?cell2) (adjacent ?cell2 ?cell3)
        )
      )

      ; row 2 should have 2 adjacent cells colored
      (exists (?cell1 ?cell2 ?cell3 ?cell4)
        (and
          (filled ?cell1) (filled ?cell2) (marked ?cell3) (marked ?cell4)
          (in-row ?cell1 row2) (in-row ?cell2 row2) (in-row ?cell3 row2) (in-row ?cell4 row2)
          (adjacent ?cell1 ?cell2)
        )
      )

      ; row 3 should have 4 adjacent cells colored
      (exists (?cell1 ?cell2 ?cell3 ?cell4)
        (and
          (filled ?cell1) (filled ?cell2) (filled ?cell3) (filled ?cell4)
          (in-row ?cell1 row3) (in-row ?cell2 row3) (in-row ?cell3 row3) (in-row ?cell4 row3)
          (adjacent ?cell1 ?cell2) (adjacent ?cell2 ?cell3) (adjacent ?cell3 ?cell4)
        )
      )

      ; Two non adjacent cells colored in line 4
      (exists (?cell1 ?cell2 ?cell3 ?cell4)
        (and
          (filled ?cell1) (filled ?cell2) (marked ?cell3) (marked ?cell4)
          (in-row ?cell1 row4) (in-row ?cell2 row4) (in-row ?cell3 row4) (in-row ?cell4 row4)
          (not(adjacent ?cell1 ?cell2))
        )
      )
    )
  )
)
