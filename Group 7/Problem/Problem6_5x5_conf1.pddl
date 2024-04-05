(define (problem nonogram_5x5_conf2)
  (:domain nonogram)
  (:objects
    cell00 cell01 cell02 cell03 cell04 - cell
    cell10 cell11 cell12 cell13 cell14 - cell
    cell20 cell21 cell22 cell23 cell24 - cell
    cell30 cell31 cell32 cell33 cell34 - cell
    cell40 cell41 cell42 cell43 cell44 - cell
    row1 row2 row3 row4 row5 - row
    col1 col2 col3 col4 col5 - col
  )

  (:init
    (empty cell00) (empty cell01) (empty cell02) (empty cell03) (empty cell04)
    (empty cell10) (empty cell11) (empty cell12) (empty cell13) (empty cell14)
    (empty cell20) (empty cell21) (empty cell22) (empty cell23) (empty cell24)
    (empty cell30) (empty cell31) (empty cell32) (empty cell33) (empty cell34)
    (empty cell40) (empty cell41) (empty cell42) (empty cell43) (empty cell44)
    (adjacent cell00 cell01) ; Specify adjacent cells in the initial state
    (adjacent cell01 cell02)
    (adjacent cell02 cell03)
    (adjacent cell03 cell04)
    (adjacent cell10 cell11)
    (adjacent cell11 cell12)
    (adjacent cell12 cell13)
    (adjacent cell13 cell14)
    (adjacent cell20 cell21)
    (adjacent cell21 cell22)
    (adjacent cell22 cell23)
    (adjacent cell23 cell24)
    (adjacent cell30 cell31)
    (adjacent cell31 cell32)
    (adjacent cell32 cell33)
    (adjacent cell33 cell34)
    (adjacent cell40 cell41)
    (adjacent cell41 cell42)
    (adjacent cell42 cell43)
    (adjacent cell43 cell44)

    (adjacent cell00 cell10)
    (adjacent cell10 cell20)
    (adjacent cell20 cell30)
    (adjacent cell30 cell40)
    (adjacent cell01 cell11)
    (adjacent cell11 cell21)
    (adjacent cell21 cell31)
    (adjacent cell31 cell41)
    (adjacent cell02 cell12)
    (adjacent cell12 cell22)
    (adjacent cell22 cell32)
    (adjacent cell32 cell42)
    (adjacent cell03 cell13)
    (adjacent cell13 cell23)
    (adjacent cell23 cell33)
    (adjacent cell33 cell43)
    (adjacent cell04 cell14)
    (adjacent cell14 cell24)
    (adjacent cell24 cell34)
    (adjacent cell34 cell44)

    (in-col cell00 col1) ; Specify column positions in the initial state
    (in-col cell01 col2)
    (in-col cell02 col3)
    (in-col cell03 col4)
    (in-col cell04 col5)
    (in-col cell10 col1)
    (in-col cell11 col2)
    (in-col cell12 col3)
    (in-col cell13 col4)
    (in-col cell14 col5)
    (in-col cell20 col1)
    (in-col cell21 col2)
    (in-col cell22 col3)
    (in-col cell23 col4)
    (in-col cell24 col5)
    (in-col cell30 col1)
    (in-col cell31 col2)
    (in-col cell32 col3)
    (in-col cell33 col4)
    (in-col cell34 col5)
    (in-col cell40 col1)
    (in-col cell41 col2)
    (in-col cell42 col3)
    (in-col cell43 col4)
    (in-col cell44 col5)

    (in-row cell00 row1) ; Specify row positions in the initial state
    (in-row cell01 row1)
    (in-row cell02 row1)
    (in-row cell03 row1)
    (in-row cell04 row1)
    (in-row cell10 row2)
    (in-row cell11 row2)
    (in-row cell12 row2)
    (in-row cell13 row2)
    (in-row cell14 row2)
    (in-row cell20 row3)
    (in-row cell21 row3)
    (in-row cell22 row3)
    (in-row cell23 row3)
    (in-row cell24 row3)
    (in-row cell30 row4)
    (in-row cell31 row4)
    (in-row cell32 row4)
    (in-row cell33 row4)
    (in-row cell34 row4)
    (in-row cell40 row5)
    (in-row cell41 row5)
    (in-row cell42 row5)
    (in-row cell43 row5)
    (in-row cell44 row5)

  )

  (:goal
    (and

      ; Column 1 should have 4 adjacent cells colored
      (exists (?cell1 ?cell2 ?cell3 ?cell4 ?cell5)
        (and
          (filled ?cell1) (filled ?cell2) (filled ?cell3) (filled ?cell4) (marked ?cell5)
          (in-col ?cell1 col1) (in-col ?cell2 col1) (in-col ?cell3 col1) (in-col ?cell4 col1) (in-col ?cell5 col1)
          (adjacent ?cell1 ?cell2) (adjacent ?cell2 ?cell3) (adjacent ?cell3 ?cell4)
        )
      )
      ; Column 2 should have 3 adjacent cells colored
      (exists (?cell1 ?cell2 ?cell3 ?cell4 ?cell5)
        (and
          (filled ?cell1) (filled ?cell2) (filled ?cell3) (marked ?cell4) (marked ?cell5)
          (in-col ?cell1 col2) (in-col ?cell2 col2) (in-col ?cell3 col2) (in-col ?cell4 col2) (in-col ?cell5 col2)
          (adjacent ?cell1 ?cell2) (adjacent ?cell2 ?cell3)
        )
      )
      ; Column 3 should have 1 cell colored
      (exists (?cell1 ?cell2 ?cell3 ?cell4 ?cell5)
        (and
          (filled ?cell1) (marked ?cell2) (marked ?cell3) (marked ?cell4) (marked ?cell5)
          (in-col ?cell1 col3) (in-col ?cell2 col3) (in-col ?cell3 col3) (in-col ?cell4 col3) (in-col ?cell5 col3)
        )
      )

      ; Two adjacent cells colored in column 4
      (exists (?cell1 ?cell2 ?cell3 ?cell4 ?cell5)
        (and
          (filled ?cell1) (filled ?cell2) (marked ?cell3) (marked ?cell4) (marked ?cell5)
          (in-col ?cell1 col4) (in-col ?cell2 col4) (in-col ?cell3 col4) (in-col ?cell4 col4) (in-col ?cell5 col4)
          (adjacent ?cell1 ?cell2)
        )
      )
      ; Column 5 should have 3 adjacent cells colored
      (exists (?cell1 ?cell2 ?cell3 ?cell4 ?cell5)
        (and
          (filled ?cell1) (filled ?cell2) (filled ?cell3) (marked ?cell4) (marked ?cell5)
          (in-col ?cell1 col5) (in-col ?cell2 col5) (in-col ?cell3 col5) (in-col ?cell4 col5) (in-col ?cell5 col5)
          (adjacent ?cell1 ?cell2) (adjacent ?cell2 ?cell3)
        )
      )

      ; row 1 should have 1 cell colored
      (exists (?cell1 ?cell2 ?cell3 ?cell4 ?cell5)
        (and
          (filled ?cell1) (marked ?cell2) (marked ?cell3) (marked ?cell4) (marked ?cell5)
          (in-row ?cell1 row1) (in-row ?cell2 row1) (in-row ?cell3 row1) (in-row ?cell4 row1) (in-row ?cell5 row1)
        )
      )
      ; row 2 should have 1 cell colored
      (exists (?cell1 ?cell2 ?cell3 ?cell4 ?cell5)
        (and
          (filled ?cell1) (marked ?cell2) (marked ?cell3) (marked ?cell4) (marked ?cell5)
          (in-row ?cell1 row2) (in-row ?cell2 row2) (in-row ?cell3 row2) (in-row ?cell4 row2) (in-row ?cell5 row2)
        )
      )

      ; two adjacent cells then one cell colored in line 3
      (exists (?cell1 ?cell2 ?cell3 ?cell4 ?cell5)
        (and
          (filled ?cell1) (filled ?cell2) (filled ?cell3) (marked ?cell4) (marked ?cell5)
          (in-row ?cell1 row3) (in-row ?cell2 row3) (in-row ?cell3 row3) (in-row ?cell4 row3) (in-row ?cell5 row3)
          (adjacent ?cell1 ?cell2) (adjacent ?cell3 ?cell4) (not(adjacent ?cell2 ?cell3)) (not(adjacent ?cell1 ?cell3))

        )
      )

      ; Two non adjacent pair of cells colored in line 4
      (exists (?cell1 ?cell2 ?cell3 ?cell4 ?cell5)
        (and
          (filled ?cell1) (filled ?cell2) (filled ?cell3) (filled ?cell4) (marked ?cell5)
          (in-row ?cell1 row4) (in-row ?cell2 row4) (in-row ?cell3 row4) (in-row ?cell4 row4) (in-row ?cell5 row4)
          (adjacent ?cell1 ?cell2) (adjacent ?cell3 ?cell4) (not(adjacent ?cell1 ?cell3)) (not(adjacent ?cell2 ?cell3)) (not(adjacent ?cell1 ?cell4)) (not(adjacent ?cell2 ?cell4))
        )
      )

      ; Row 5 has 4 adjacent filled cells
      (exists (?cell1 ?cell2 ?cell3 ?cell4 ?cell5)
        (and
          (filled ?cell1) (filled ?cell2) (filled ?cell3) (filled?cell4) (marked ?cell5)
          (in-row ?cell1 row5) (in-row ?cell2 row5) (in-row ?cell3 row5) (in-row ?cell4 row5) (in-row ?cell5 row5)
          (adjacent ?cell1 ?cell2) (adjacent ?cell2 ?cell3) (adjacent ?cell3 ?cell4) 
        )
      )
    )
  )
)
