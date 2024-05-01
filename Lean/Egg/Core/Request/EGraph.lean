import Egg.Core.Request.Basic

namespace Egg

private opaque EGraph.Pointed : NonemptyType

def EGraph := EGraph.Pointed.type

instance : Nonempty EGraph := EGraph.Pointed.property

@[extern "run_egg_request"]
opaque Request.run (req : Request) : IO (Explanation.Raw × EGraph)
