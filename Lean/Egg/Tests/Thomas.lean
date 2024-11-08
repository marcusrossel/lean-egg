import Egg

-- With union semantics, this never terminates. Using the `vizPath` output, we can see that it only
-- runs 5 iterations. Further investigation shows that we encounter a loop in the e-class analysis
-- of loose bvars as part of a looping shift-node.

set_option egg.unionSemantics false in
example :
    ((fun x => (fun t (_y : α) => t) (fun z => x z)) (fun (z : α → α → α) x => ((fun _y => z) x) x))
    = fun _y => (fun z => z) := by
  egg
