/-
Copyright (c) 2025 Davood H. T. Tehrani, David Gross. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davood H. T. Tehrani, David Gross
-/
import Mathlib.Data.List.Basic

/-!
# A First-Order Language for Arithmetic

This file defines the syntax and semantics of a minimal first-order language
with symbols for `0`, successor, addition, and multiplication.
Variables are indexed by `Nat` and interpreted using a list as memory.
-/

------ Language Syntax

inductive Term  where
  | zero : Term
  | var  : Nat → Term -- Use Nat's to label variables.
  | succ : Term → Term
  | add  : Term → Term → Term
  | mul  : Term → Term → Term

inductive Formula where
  | eq     : Term → Term → Formula
  | not    : Formula → Formula
  | and    : Formula → Formula → Formula
  | exists : Formula → Formula  -- Existential quantifier. Introduces new variable at head of list.

------ Language Semantics

/-- A model gives meaning to non-logical symbols -/
class Model (domain : Type) where
  succ : domain → domain
  [zero : Zero domain]
  [add : Add domain]
  [mul: Mul domain]

attribute [reducible] Model.succ
attribute [reducible] Model.add
attribute [reducible] Model.zero
attribute [reducible] Model.mul

instance {domain : Type} [m : Model domain] : Inhabited domain where
  default := m.zero.zero

-- Example of Standard Nat model. Everything is inferred except for successor function.
instance NatModel : Model Nat where
  succ := Nat.succ

def varListInit (domain : Type) : List domain := List.nil

/--
Lookup of a variable by index.
If the index is out of range, `0` is returned via `Inhabited`.
-/
def getVar {domain : Type} [Model domain] : List domain → Nat → domain :=
  fun v n => List.getI v n

/--
Extend a variable assignment by adding a new variable
at the head of the list. This corresponds to binding
a variable under an existential quantifier.
-/
def setVar {domain : Type} : List domain → domain → List domain :=
  fun v x => List.cons x v

/--
Interpret a term in a given model and variable assignment.
-/
def interpretTerm {domain} [m : Model domain] : List domain → Term → domain := fun v t =>
  match t with
  | Term.zero      => m.zero.zero
  | Term.succ s    => m.succ (interpretTerm v s)
  | Term.add s1 s2 => m.add.add (interpretTerm v s1) (interpretTerm v s2)
  | Term.mul s1 s2 => m.mul.mul (interpretTerm v s1) (interpretTerm v s2)
  | Term.var i     => getVar v i

/--
Interpret Formulas.
It should only be called with a /sentence/, i.e. a formula with no free vars.
Any free vars will be set to zero in `interpretTerm`.
-/
def interpret {domain} [m : Model domain] : List domain → Formula → Prop := fun v f =>
  match f with
  | Formula.eq t1 t2  => Eq (interpretTerm v t1) (interpretTerm v t2)
  | Formula.not g     => Not (interpret v g)
  | Formula.and g1 g2 => And (interpret v g1) (interpret v g2)
  /- interpret g in a context where i-th var has been set to xi for exists -/
  | Formula.exists g => Exists (fun x : domain => interpret (setVar v x) g)


@[simp] lemma interpret_eq {domain} [Model domain] (t1 t2) (v : List domain) :
  interpret v (Formula.eq t1 t2) ↔ (interpretTerm v t1) = (interpretTerm v t2) := by rfl

@[simp] lemma interpret_not {domain} [Model domain] (f) (v : List domain) :
  interpret v f.not ↔ ¬ interpret v f := by rfl

@[simp] lemma interpret_and {domain} [Model domain] (f g : Formula) (v : List domain) :
  interpret v (f.and g) ↔ interpret v f ∧ interpret v g := by rfl

@[simp] lemma interpret_exists {domain} [Model domain] (f : Formula) (v : List domain) :
  interpret v f.exists ↔ Exists (fun x : domain => interpret (setVar v x) f) := by rfl
