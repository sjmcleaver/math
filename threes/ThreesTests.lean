import Threes

def makeGame(s : BoardState) : GameState := {
  board := s,
  next := { first := 1, second := none, third := none },
  invalid := false
}

def maxBoard : GameState :=
  makeGame {
    a := { x := 1, y := 2, z := 3, w := 4 },
    b := { x := 5, y := 6, z := 7, w := 8 },
    c := { x := 9, y := 10, z := 11, w := 12 },
    d := { x := 13, y := 14, z := 15, w := 16 }
  }

def onesBoard : GameState :=
  makeGame {
    a := { x := 1, y := 1, z := 1, w := 1 },
    b := { x := 1, y := 1, z := 1, w := 1 },
    c := { x := 1, y := 1, z := 1, w := 1 },
    d := { x := 1, y := 1, z := 1, w := 1 }
  }

#eval maxBoard
#eval transpose maxBoard
#eval shiftLeft onesBoard
#eval shiftLeft (shiftLeft onesBoard)
#eval shiftLeft (shiftLeft (shiftLeft onesBoard))
#eval shiftRight onesBoard