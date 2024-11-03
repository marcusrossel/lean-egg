namespace Egg

private opaque EGraph.Pointed : NonemptyType.{0}

def EGraph.Obj := EGraph.Pointed.type

instance : Nonempty EGraph.Obj := EGraph.Pointed.property

structure EGraph where
  obj     : EGraph.Obj
  slotted : Bool
