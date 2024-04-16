# Equality Saturation Tactic for Lean

This repository contains a (work-in-progress) _equality saturation_ tactic for [Lean](https://lean-lang.org) based on [egg](https://egraphs-good.github.io). The tactic is useful for automated equational reasoning based on given equational theorems. Checkout the `Lean/Egg/Tests` directory for examples.

## Setup

This tactic requires you to have the programming language _Rust_ and its package manager _Cargo_ installed. 
These are easily installed following the [official guide](https://doc.rust-lang.org/cargo/getting-started/installation.html).

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
theorem reverse_append (as bs : List α) : reverse (as ++ bs) = (reverse bs) ++ (reverse as) := by
  induction as generalizing bs with
  | nil          => egg [reverse_nil, append_nil, append]
  | cons a as ih => egg [ih, append_assoc, reverse_cons, append]
```

But you can use it to solve some equations which `simp` cannot:

```lean
import Egg
import Std

variable (a b c d : Int)

example : ((a * b) - (2 * c)) * d - (a * b) = (d - 1) * (a * b) - (2 * c * d) := by
  egg [Int.sub_mul, Int.sub_sub, Int.add_comm, Int.mul_comm, Int.one_mul]
```

Sometimes, `egg` needs a little help with finding the correct sequence of rewrites.
You can help out by providing _guide terms_ with nudge `egg` to try certain paths:

```lean
-- From Lean/Egg/Tests/Groups.lean

theorem inv_inv [Group G] (a : G) : -(-a) = a := by
  egg [/- group axioms -/] using -a + a
```

And if you want to prove your goal based on an equivalent hypothesis, you can use the `from` syntax:

```lean
variable (and_assoc : ∀ a b c, (a ∧ b) ∧ c ↔ a ∧ (b ∧ c)) (and_idem : ∀ a, a ↔ a ∧ a)

example (h : p ∧ q ∧ r) : r ∧ r ∧ q ∧ p ∧ q ∧ r ∧ p := by
  egg [And.comm, and_assoc, and_idem] from h
```