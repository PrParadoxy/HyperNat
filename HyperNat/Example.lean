/-
Copyright (c) 2025 Davood H. T. Tehrani, David Gross. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davood H. T. Tehrani, David Gross
-/
import «HyperNat».Los
import Mathlib.Algebra.Ring.Parity

/-!

In this file, we show a rather counter intuitive example of hyper natural numbers.
Take the quotient of sequence `[0, 1, 2, ...]` as a hyper natural.
We prove that it is either `even` or `odd`.

-/


abbrev one : Term := Term.succ (Term.zero)

abbrev two : Term := Term.succ one

#eval interpretTerm ([] : List Nat) one
#eval interpretTerm ([] : List Nat) two

abbrev is_twice : Nat → Nat → Formula := fun i j =>
  Formula.eq
    (Term.var i)
    (Term.mul two (Term.var j))

abbrev is_twice_plus_one : Nat → Nat → Formula := fun i j =>
  Formula.eq
    (Term.var i)
    (Term.add
      (Term.mul two (Term.var j))
      one
    )

/--
Statement that i-th var is even,
i.e. that there exists a y such that x_i = 2 * y.

Complication: y needs to be stored in a var.
The existence quantifier is hard-coded such that the new var will be placed at head of list,
shifting all vars.
-/
abbrev even : Nat → Formula := fun i => Formula.exists (is_twice (i + 1) 0)

abbrev odd : Nat → Formula := fun i => Formula.exists (is_twice_plus_one (i + 1) 0)

-- Statement that every element of the domain is even or odd
abbrev even_or_odd : Nat → Formula  := fun i =>
    Formula.not
    (Formula.and
      (Formula.not (even i))
      (Formula.not (odd i))
    )

abbrev all_are_even_or_odd : Formula :=
  Formula.not
    (Formula.exists
      (Formula.not (even_or_odd 0)
    )
  )

/-- 2 is twice as 1. -/
example : interpret [2, 1] (is_twice 0 1) := by rfl

set_option linter.flexible false in
theorem all_are_even_or_odd_nat : interpret ([] : List Nat) all_are_even_or_odd := by
  simp
  intro x h
  have hnat := Nat.even_or_odd x
  unfold Even Odd at hnat
  simp [← Nat.mul_two] at hnat
  apply Or.elim hnat
  · intro h1
    let ⟨w, hw⟩ := h1
    rw [Nat.mul_comm] at hw
    use w
    exfalso
    exact (h w) hw
  · exact id

def all_are_even_or_odd_hypnat (p : PrimeIdeal)
    : interpret ([] : List (HypNat p)) all_are_even_or_odd :=
  (hyperNat_transfer p all_are_even_or_odd).mpr all_are_even_or_odd_nat

def inc_seq (p : PrimeIdeal) : (HypNat p) := ⟦fun i => i⟧

lemma inc_seq_is_even_or_odd (p : PrimeIdeal) : interpret [inc_seq p] (even_or_odd 0) := by
  have hall := all_are_even_or_odd_hypnat p
  simp_all only [interpret_not, interpret_exists, interpret_and, zero_add, interpret_eq,
    change_model, not_exists, not_and, not_forall, not_not]
  exact hall (inc_seq p)
