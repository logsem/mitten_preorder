type mode = String

type m = String

type cell =
  |  Atom of string
  | HComp of cell * cell
  |  VComp of cell * cell
