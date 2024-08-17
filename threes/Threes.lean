import Mathlib

-- def Strategy := State → P(State)

-- def Game := FSA(Set(State), ∅, δ: Strategy, q : InitialState, Set(FinalState))


def Index := LinearOrder (Fin 4)
def Tile := ℕ

inductive Axis
| vertical
| horizontal

inductive Direction
| positive
| negative

def Move := (Axis, Direction)

def Row := Index → Tile

def Board := Index → Row

def transpose(b : Board) : Board := fun i : Index  => fun j : Index => b j i

structure NextTileState where
  first : Nat
  second : Option Nat
  third : Option Nat
deriving Repr

structure GameState where
  board : Board
  next : NextTileState
  invalid : Bool
deriving Repr

def shiftRowLeft(r : Row) : Row :=
  match r.x with
  | Nat.zero => { x := r.y, y := r.z, z := r.w, w := Nat.zero }
  | Nat.succ _ => match (r.x == r.y) with
    | true => { x := r.x + r.y, y := r.z, z := r.w, w := Nat.zero }
    | false => match (r.y == r.z) with
      | true => { x := r.x, y := r.y + r.z, z := r.w, w := Nat.zero }
      | false => match (r.z == r.w) with
        | true => { x := r.x, y := r.y, z := r.z + r.w, w := Nat.zero }
        | false => r -- illegal shift

def shiftRowRight(r : Row) : Row := reverse (shiftRowLeft (reverse r))

def shiftLeft(s : Board) : Board := {
  a := shiftRowLeft s.a,
  b := shiftRowLeft s.b,
  c := shiftRowLeft s.c,
  d := shiftRowLeft s.d
}

def shiftRight(s : Board) : Board := {
  a := shiftRowRight s.a,
  b := shiftRowRight s.b,
  c := shiftRowRight s.c,
  d := shiftRowRight s.d
}

def shiftUp(s : Board) : Board := transpose (shiftLeft (transpose s))
def shiftDown(s : Board) : Board := transpose (shiftRight (transpose s))

def isRowShiftLegal(d: Direction)(r : Row) : Bool :=
  match d with
  | right => 
    r.x == 0 || r.x == r.y ||
    r.y == 0 || r.y == r.z ||
    r.z == 0 || r.z == r.w


def isShiftLegal(d : Direction)(s : Board) : Bool :=
  match d with
  | left =>
      isRowShiftLegal s.a ||
      isRowShiftLegal s.b ||
      isRowShiftLegal s.c ||
      isRowShiftLegal s.d
  | up => isShiftLegal left (transpose s)


def legalShift(d : Direction)(s : GameState) : GameState := {
  board := match d with
    | left => shiftLeft s.board
    | right => shiftRight s.board
    | up => shiftUp s.board
    | down => shiftDown s.board,
  next := s.next,
  invalid := s.invalid
}

def invalidate(s : GameState) : GameState := {
  board := s.board,
  next := s.next,
  invalid := true
}

def shift(d : Direction)(s : GameState) : GameState :=
  match isShiftLegal d s.board with
  | false => invalidate s
  | true => legalShift d s


