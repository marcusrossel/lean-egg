# <img src="Docs/icon.png" alt="lean-egg logo" height="38" align="left"> Equality Saturation Tactic for Lean

This repository contains a (work-in-progress) [equality saturation](https://arxiv.org/abs/1012.1802) tactic for [Lean](https://lean-lang.org) based on [egg](https://egraphs-good.github.io). This `egg` tactic is useful for automated equational reasoning based on given equational theorems. 

## Setup

The `egg` tactic requires [Rust](https://www.rust-lang.org) and its package manager [Cargo](https://doc.rust-lang.org/cargo/). 
They are easily installed following the [official guide](https://doc.rust-lang.org/cargo/getting-started/installation.html).

To use `egg` in your Lean project, add the following line to your `lakefile.toml`:

```toml
[[require]]
name = "egg"
git  = "https://github.com/marcusrossel/lean-egg"
rev  = "main"
```

... or the following line to your `lakefile.lean`:

```lean
require "marcusrossel" / "egg" @ git "main"
```

Then, add `import Egg` to the files that require `egg`.

## Basic Usage

The syntax of `egg` is very similar to that of `simp` or `rw`:

```lean
import Egg

example : 0 = 0 := by
  egg

example (a b c : Nat) (h₁ : a = b) (h₂ : b = c) : a = c := by
  egg [h₁, h₂]

open List in
example (as bs : List α) : reverse (as ++ bs) = (reverse bs) ++ (reverse as) := by
  induction as generalizing bs with
  | nil  => egg [reverse_nil, append_nil, List.append]
  | cons => egg [*, append_assoc, reverse_cons, List.append]
```

But you can use it to solve some equations which `simp` cannot:

```lean
import Egg

variable (a b c d : Int)

example : ((a * b) - (2 * c)) * d - (a * b) = (d - 1) * (a * b) - (2 * c * d) := by
  egg [Int.sub_mul, Int.sub_sub, Int.add_comm, Int.mul_comm, Int.one_mul]
```

Sometimes, `egg` needs a little help with finding the correct sequence of rewrites.
You can help out by providing _guide terms_ which nudge `egg` in the right direction:

```lean
import Mathlib.Algebra.Group.Defs
import Egg

example [Group G] (a : G) : a⁻¹⁻¹ = a := by
  egg [/- group axioms -/] using a⁻¹ * a
```

If you need more control, you can use `egg calc` to specify a chain of equations:

```lean
-- From `Lean/Egg/Tests/Freshman Calc.lean`
import Egg

example [CharTwoRing α] (x y : α) : (x + y) ^ 3 = x ^ 3 + x * y ^ 2 + x ^ 2 * y + y ^ 3 := by
  egg calc [/- axioms of ring of characteristic 2 -/]
    _ = (x + y) * (x + y) * (x + y)
    _ = (x + y) * (x * (x + y) + y * (x + y))
    _ = (x + y) * (x ^ 2 + y ^ 2)
    _ = x * (x ^ 2 + y ^ 2) + y * (x ^ 2 + y ^ 2)
    _ = (x * x ^ 2) + x * y ^ 2 + y * x ^ 2 + y * y ^ 2
    _ = _
```

For conditional rewriting, hypotheses can be provided alongside rewrites:

```lean
import Egg

example {p q r : Prop} (h₁ : p) (h₂ : p ↔ q) (h₃ : q → (p ↔ r)) : p ↔ r := by
  egg [h₁, h₂, h₃]
```

Note that rewrites are also applied to hypotheses.

## Related Work

* [An Equality Saturation Tactic for Lean](https://cfaed.tu-dresden.de/files/Images/people/chair-cc/theses/2407_Rossel_MA.pdf) contains a detailed description of the tactic's inner workings as of June 2024.
* [Guided Equality Saturation](https://dl.acm.org/doi/10.1145/3632900) introduces the original prototype of the `egg` tactic.
* [Bridging Syntax and Semantics of Lean Expressions in E-Graphs](http://arxiv.org/abs/2405.10188) contains a high-level description of how the tactic handles binders and definitional equality. 
