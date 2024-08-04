# Equality Saturation Tactic for Lean

This repository contains a (work-in-progress) [equality saturation](https://arxiv.org/abs/1012.1802) tactic for [Lean](https://lean-lang.org) based on [egg](https://egraphs-good.github.io). The tactic is useful for automated equational reasoning. Checkout the `Lean/Egg/Tests` directory for examples.

## Setup

This tactic requires [Rust](https://www.rust-lang.org) and its package manager [Cargo](https://doc.rust-lang.org/cargo/). 
They are easily installed following the [official guide](https://doc.rust-lang.org/cargo/getting-started/installation.html).

To use `egg` in your Lean project, add the following line to your `lakefile.lean`:

```lean
require egg from git "https://github.com/marcusrossel/lean-egg" @ "main"
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
  | nil         => egg [reverse_nil, append_nil, append]
  | cons _ _ ih => egg [ih, append_assoc, reverse_cons, append]
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
-- From Lean/Egg/Tests/Groups.lean
import Egg

example [Group G] (a : G) : a⁻¹⁻¹ = a := by
  egg [/- group axioms -/] using a⁻¹ * a
```

And if you want to prove your goal based on an equivalent hypothesis, you can use the `from` syntax:

```lean
import Egg

example (h : p ∧ q ∧ r) : r ∧ r ∧ q ∧ p ∧ q ∧ r ∧ p := by
  egg [and_comm, and_assoc, and_self] from h
```

For conditional rewriting, hypotheses can be provided after the rewrites:

```lean
import Egg

example {p q r : Prop} (h₁ : p) (h₂ : p ↔ q) (h₃ : q → (p ↔ r)) : p ↔ r := by
  egg [h₂, h₃; h₁]
```

Note that rewrites are also applied to hypotheses.

## Related Work

* [An Equality Saturation Tactic for Lean](https://cfaed.tu-dresden.de/files/Images/people/chair-cc/theses/2407_Rossel_MA.pdf) contains a detailed description of the tactic's inner workings as of June 2024.
* [Guided Equality Saturation](https://dl.acm.org/doi/10.1145/3632900) introduces the original prototype of the `egg` tactic.
* [Bridging Syntax and Semantics of Lean Expressions in E-Graphs](http://arxiv.org/abs/2405.10188) contains a high-level description of how the tactic handles binders and definitional equality. 
