open Util.Naming

type dimctx = variable list

let empty = []

let weaken (context : dimctx) (v : variable) : dimctx =
  v::context

let check (context : dimctx) (v : variable) : bool =
  (List.mem v context)

let make (l : 'a list) : dimctx =
  l

let initial : dimctx = []
