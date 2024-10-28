import Egg

-- BUG: This never terminates. But using the `vizPath` output, we can see that it only runs 5
--      iterations. Thus, we're probably encountering a loop in the e-class analysis of loose bvars.
--      Since we have special handling for this in the case of a direct shift loop, this example
--      probablyc produces a setting where the shift loop involves at least one other intermediate
--      e-class.c
example :
    ((fun x => (fun t (_y : α) => t) (fun z => x z)) (fun (z : α → α → α) x => ((fun _y => z) x) x))
    = fun y => (fun z => z) := by
  sorry -- egg (config := { vizPath := "/Users/marcus/Desktop/dot" })
