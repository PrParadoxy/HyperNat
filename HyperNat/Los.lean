/-
Copyright (c) 2025 Davood H. T. Tehrani, David Gross. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davood H. T. Tehrani, David Gross
-/
import «HyperNat».Def
import «HyperNat».Lang


open HypNat BooleanIdeal

/-- The model of hyper natural numbers -/
instance HypModel (I : BooleanIdeal) : Model (HypNat I) where
  succ := HypNat.succ

variable {I : BooleanIdeal}

noncomputable def toNatList (v : List (HypNat I)) : Nat → List Nat :=
  fun n => v.map (fun a => a.out n)

lemma toNatList_setvar (v : List (HypNat I)) (w) :
    ∀ i, (toNatList (setVar v w) i) = (setVar (toNatList v i) (w.out i)) := by
  simp [setVar, toNatList]

@[simp] lemma change_model (t) (v : List (HypNat I)) :
    interpretTerm v t = ⟦fun i => interpretTerm (toNatList v i) t⟧ := by
  induction t with
  | zero => exact mk_zero
  | succ _ ih => exact congrArg succ ih
  | add _ _ ih1 ih2 => exact congrArg₂ add ih1 ih2
  | mul _ _ ih1 ih2 => exact congrArg₂ mul ih1 ih2
  | var a =>
    induction v generalizing a with
    | nil => exact mk_zero
    | cons h _ ih =>
      cases a with
      | zero => exact (Quotient.out_eq h).symm
      | succ n => exact ih n

/--
Łoś theorem for hyper natural numbers.

Let `p` be a `PrimeIdeal`.
A formula holds for a list `v` of `HypNat` variables
if and only if the set of indices `i` where the formula fails
for the componentwise representatives lies in `p`.

Equivalently, a first-order formula is true in the ultrapower
exactly when it holds on a `p`-large set of indices.
-/
theorem Los {p : PrimeIdeal} (v : List (HypNat p)) (f : Formula) :
    interpret v f ↔ { i | ¬ interpret (toNatList v i) f } ∈ p := by
  induction f generalizing v with
  | eq t₁ t₂ =>
    simp only [interpret_eq, change_model]
    exact ⟨fun h => Quotient.eq.mp h,
      fun h => Quotient.eq_iff_equiv.mpr ((Setoid_rel_iff ..).mpr h)⟩
  | not a ih =>
    rw [p.mem_iff_compl_not_mem]
    simpa [not_iff_not] using ih v
  | and a b ih1 ih2 =>
    simp only [interpret_and, not_and_or, Set.setOf_or]
    exact ⟨fun h => p.closed ((ih1 v).mp h.left) ((ih2 v).mp h.right),
      fun h => ⟨(ih1 v).mpr (undo_union_left h), (ih2 v).mpr (undo_union_right h)⟩⟩
  | «exists» a ih =>
    simp only [interpret_exists, not_exists]
    refine ⟨fun h => downward_closed ((ih (setVar v h.choose)).mp h.choose_spec)
      (fun i h₂ => h₂ (h.choose.out i)), fun h => ?_⟩
    classical
    let q : ℕ → ℕ := fun i =>
      if h : ∃ x, interpret (setVar (toNatList v i) x) a then h.choose else 0
    use ⟦q⟧
    apply (ih (setVar v ⟦q⟧)).mpr
      (downward_closed (p.closed (Quotient.mk_out q) h) (fun n h₁ => ?_))
    simp_all only [Set.mem_setOf_eq, Set.mem_union]
    apply Decidable.not_or_of_imp (fun h₂ => ?_)
    by_contra! hc
    simp only [toNatList_setvar, h₂, hc, q] at h₁
    exact h₁ hc.choose_spec

/--
`Transfer principle`:
Hyper natural numbers model every true statement about standard natural numbers.
-/
theorem hyperNat_transfer (p : PrimeIdeal) (f : Formula) :
    interpret (List.nil : List (HypNat p)) f ↔ interpret (List.nil : List Nat) f := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · replace h := (Los List.nil f).mp h
    rw [p.mem_iff_compl_not_mem] at h
    have h : Nonempty {x | interpret (toNatList (I := p) [] x) f} := by
      refine Set.nonempty_iff_ne_empty'.mpr (fun h₁ => ?_)
      simp only [Set.compl_def, Set.mem_setOf_eq, not_not, h₁] at h
      exact h (p.empty_mem)
    simpa [toNatList] using h
  · apply (Los List.nil f).mpr
    convert p.empty_mem
    simp only [toNatList, List.map_nil]
    grind
