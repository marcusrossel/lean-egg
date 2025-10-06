import Egg

-- Note: To find theorems which are not solved by `grind`, search for `solved_by simp` or `sorry`.

open Lean Meta Elab Term Tactic
elab "solved_by " grind?:"grind"? simp?:"simp"? : tactic => do
  match grind?, simp? with
  | none,   none   => throwError "Provide 'grind' or 'simp' or both."
  | some _, none   => _ ← runTactic (← getMainGoal) (← `(tactic| grind))
  | none,   some _ => _ ← runTactic (← getMainGoal) (← `(tactic| (simp [*]; done)))
  | some _, some _ =>
    let state ← saveState
    _ ← runTactic (← getMainGoal) (← `(tactic| grind))
    state.restore
    _ ← runTactic (← getMainGoal) (← `(tactic| (simp [*]; done)))

inductive Vec (α : Type _) : Nat → Type _ where
  | nil : Vec α 0
  | cons (hd : α) (tl : Vec α n) : Vec α (n + 1)

namespace Vec

notation "[]ᵥ" => Vec.nil
infixr:67 " ::ᵥ " => Vec.cons

@[grind, simp]
def append : Vec α n → Vec α m → Vec α (m + n)
  | []ᵥ,      bs => bs
  | a ::ᵥ as, bs => a ::ᵥ (append as bs)

infixr:67 " ++ᵥ " => Vec.append

@[grind, simp]
def map (f : α → β) : Vec α n → Vec β n
  | []ᵥ      => []ᵥ
  | a ::ᵥ as => f a ::ᵥ map f as

@[grind, simp]
def take : (n : Nat) → Vec α (m + n) → Vec α n
  | 0,     _        => []ᵥ
  | n + 1, a ::ᵥ as => a ::ᵥ (take n as)

@[grind, simp]
def drop : (n : Nat) → Vec α (m + n) → Vec α m
  | 0,     as       => as
  | n + 1, _ ::ᵥ as => drop n as

@[grind, simp]
def split (n : Nat) : {m : Nat} → Vec α (n * m) → Vec (Vec α n) m
  | 0,     _  => []ᵥ
  | _ + 1, as => take n as ::ᵥ split n (drop n as)

@[grind, simp]
def join : Vec (Vec α n) m → Vec α (n * m)
  | []ᵥ      => []ᵥ
  | a ::ᵥ as => a ++ᵥ join as

@[grind, simp]
def reduceSeq (f : α → β → β) (init : β) : Vec α n → β
  | []ᵥ      => init
  | a ::ᵥ as => reduceSeq f (f a init) as

@[grind, simp]
def head : Vec α (n + 1) → α
  | a ::ᵥ _ => a

@[grind, simp]
def tail : Vec α (n + 1) → Vec α n
  | _ ::ᵥ as => as

@[grind, simp]
def fill (a : α) : (n : Nat) → Vec α n
  | 0     => []ᵥ
  | n + 1 => a ::ᵥ fill a n

@[grind, simp]
def transpose : {n m : Nat} → Vec (Vec α m) n → Vec (Vec α n) m
  | _ + 1, 0,     _   => []ᵥ
  | 0,     _,     []ᵥ => fill []ᵥ _
  | _ + 1, _ + 1, as  => map head as ::ᵥ transpose (map tail as)

-- Note: For this theorem `egg` needs to understand addition to handle syntactic differences at the type level.
@[grind _=_, simp]
theorem map_take (f : α → β) (as : Vec α (m + n)) : map f (take n as) = take n (map f as) := by
  induction n <;> try cases as
  all_goals solved_by simp

-- Note: We don't tag this with `@[grind, simp]` as it is not a theorem which is suitable for pattern matching.
theorem fill_nil (as : Vec (Vec α 0) n) : fill []ᵥ n = as := by
  induction as <;> try cases ‹Vec _ 0›
  all_goals solved_by grind simp

@[grind, simp]
theorem fill_nil₂ (as : Vec α n) : map tail (transpose (as ::ᵥ []ᵥ)) = fill []ᵥ n := by
  induction as
  all_goals solved_by grind simp

-- Note: For this theorem `egg` needs to understand addition to handle syntactic differences at the type level.
@[grind _=_, simp]
theorem map_drop (f : α → β) (as : Vec α (m + n)) : map f (drop n as) = (drop n (map f as)) := by
  induction n generalizing m <;> cases as
  all_goals solved_by simp

@[grind, simp]
theorem take_drop (as : Vec α (m + n)) : take n as ++ᵥ drop n as = as := by
  induction n generalizing m <;> cases m <;> cases as
  all_goals solved_by grind simp

-- Note: For this theorem `egg` needs to understand multiplication to handle syntactic differences at the type level.
@[grind _=_, simp]
theorem map_split (f : α → β) (as : Vec α (n * m)) : map (map f) (split n as) = split n (map f as) := by
  induction m
  all_goals solved_by grind simp

@[grind _=_, simp]
theorem map_head (f : α → β) (as : Vec (Vec α (m + 1)) n) : map f (map head as) = map head (map (map f) as) := by
  induction as <;> try cases ‹Vec _ (_ + 1)›
  all_goals solved_by grind simp

@[grind _=_, simp]
theorem map_tail (f : α → β) (as : Vec (Vec α (m + 1)) n) : map (map f) (map tail as) = map tail (map (map f) as) := by
  induction as <;> try cases ‹Vec _ (_ + 1)›
  all_goals solved_by grind simp

-- Note: This theorem takes a while.
@[grind, simp]
theorem map_tail_trans (a : Vec α (m + 1)) (as : Vec (Vec α (m + 2)) (n + 1)) : map tail (transpose (tail a ::ᵥ map tail (map tail as))) = transpose (map tail (map tail as)) := by
  induction m <;> cases a
  all_goals solved_by grind

-- Note: This theorem takes a while.
@[grind, simp]
theorem transpose_head (a : Vec α n) (as : Vec (Vec α (n + 1)) m) : map head (transpose (a ::ᵥ map tail as)) = a := by
  induction n <;> cases a
  all_goals solved_by grind simp

-- Note: This theorem takes a while.
@[grind, simp]
theorem transpose_tail (a : Vec α n) (as : Vec (Vec α (n + 1)) m) : map head as ::ᵥ map tail (transpose (a ::ᵥ map tail as)) = transpose as := by
  cases n <;> cases m <;> cases as
  all_goals solved_by grind

@[grind, simp]
theorem simplification₁ (as : Vec α (n * m)) : join ((split n) as) = as := by
  induction m <;> try cases as
  all_goals solved_by grind simp

/-- Figure 6: Rule 2 -/
@[grind, simp]
theorem id_to_transpose (as : Vec (Vec α m) n) : transpose (transpose as) = as := by
  induction n <;> cases m <;> cases as <;> try cases ‹Vec _ (_ + 1)›
  all_goals
    try have := fill_nil (‹_› ::ᵥ ‹_›)
    solved_by grind

/-- Figure 6: Rule 3 -/
@[grind _=_, simp]
theorem transpose_move (f : α → β) (as : Vec (Vec α n) m) : map (map f) (transpose as) = transpose (map (map f) as) := by
  induction n <;> cases m <;> cases as <;> try cases ‹Vec _ (_ + 1)›
  fail_if_success all_goals (simp [*]; done)
  fail_if_success all_goals grind
  all_goals sorry

/-- Figure 6: Rule 4 -/
@[grind _=_, simp]
theorem split_join (n : Nat) (f : α → β) (as : Vec α (n * m)) : (join ∘ (map (map f)) ∘ split n) as = map f as := by
  solved_by grind simp

/-- Figure 6: Rule 5 -/
@[grind _=_, simp]
theorem map_fusion (f : β → γ) (g : α → β) (as : Vec α n) : (map f ∘ map g) as = map (f ∘ g) as := by
  induction as
  all_goals solved_by grind

/-- Figure 6: Rule 6 -/
@[grind, simp]
theorem fuse_reduce_map (f : α → β) (bf : β → γ → γ) (init : γ) (as : Vec α n) : reduceSeq (fun a b => bf (f a) b) init as = (reduceSeq bf init ∘ map f) as := by
  induction as generalizing init
  all_goals solved_by grind simp
