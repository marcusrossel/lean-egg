namespace Egg

private opaque EGraph.Pointed : NonemptyType.{0}

def EGraph := EGraph.Pointed.type

instance : Nonempty EGraph := EGraph.Pointed.property
