/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll, Mario Carneiro, Robert Y. Lewis
-/
import Mathlib.Tactic.Basic
import Mathlib.Tactic.NormCast
import Mathlib.Data.Int.Basic

/-!
# `zify` tactic

The `zify` tactic is used to shift propositions from `ℕ` to `ℤ`.
This is often useful since `ℤ` has well-behaved subtraction.
```
example (a b c x y z : ℕ) (h : ¬ x*y*z < 0) : c < a + 3*b := by
  zify
  zify at h
  /-
  h : ¬↑x * ↑y * ↑z < 0
  ⊢ ↑c < ↑a + 3 * ↑b
  -/
```
-/

namespace Mathlib.Tactic.Zify

open Lean
open Lean.Meta
open Lean.Parser.Tactic
open Lean.Elab.Tactic

/--
The `zify` tactic is used to shift propositions from `ℕ` to `ℤ`.
This is often useful since `ℤ` has well-behaved subtraction.
```
example (a b c x y z : ℕ) (h : ¬ x*y*z < 0) : c < a + 3*b := by
  zify
  zify at h
  /-
  h : ¬↑x * ↑y * ↑z < 0
  ⊢ ↑c < ↑a + 3 * ↑b
  -/
```
`zify` can be given extra lemmas to use in simplification. This is especially useful in the
presence of nat subtraction: passing `≤` arguments will allow `push_cast` to do more work.
```
example (a b c : ℕ) (h : a - b < c) (hab : b ≤ a) : false := by
  zify [hab] at h
  /- h : ↑a - ↑b < ↑c -/
```
`zify` makes use of the `@[zify_simps]` attribute to move propositions,
and the `push_cast` tactic to simplify the `ℤ`-valued expressions.
`zify` is in some sense dual to the `lift` tactic. `lift (z : ℤ) to ℕ` will change the type of an
integer `z` (in the supertype) to `ℕ` (the subtype), given a proof that `z ≥ 0`;
propositions concerning `z` will still be over `ℤ`. `zify` changes propositions about `ℕ` (the
subtype) to propositions about `ℤ` (the supertype), without changing the type of any variable.
-/
syntax (name := zify) "zify" (simpArgs)? (location)? : tactic

macro_rules
| `(tactic| zify $[[$simpArgs,*]]? $[at $location]?) =>
  let args := simpArgs.map (·.getElems) |>.getD #[]
  `(tactic|
    simp (config := {decide := false}) only [zify_simps, push_cast, $args,*] $[at $location]?)

/-- The `Simp.Context` generated by `zify`. -/
def mkZifyContext (simpArgs : Option (Syntax.TSepArray `Lean.Parser.Tactic.simpStar ",")) :
    TacticM MkSimpContextResult := do
  let args := simpArgs.map (·.getElems) |>.getD #[]
  mkSimpContext
    (← `(tactic| simp (config := {decide := false}) only [zify_simps, push_cast, $args,*])) false

/-- A variant of `applySimpResultToProp` that cannot close the goal, but does not need a meta
variable and returns a tuple of a proof and the corresponding simplified proposition. -/
def applySimpResultToProp' (proof : Expr) (prop : Expr) (r : Simp.Result) : MetaM (Expr × Expr) :=
  do
  match r.proof? with
  | some eqProof => return (← mkExpectedTypeHint (← mkEqMP eqProof proof) r.expr, r.expr)
  | none =>
    if r.expr != prop then
      return (← mkExpectedTypeHint proof r.expr, r.expr)
    else
      return (proof, r.expr)

/-- Translate a proof and the proposition into a zified form. -/
def zifyProof (simpArgs : Option (Syntax.TSepArray `Lean.Parser.Tactic.simpStar ","))
    (proof : Expr) (prop : Expr) : TacticM (Expr × Expr) := do
  let ctx_result ← mkZifyContext simpArgs
  let (r, _) ← simp prop ctx_result.ctx
  applySimpResultToProp' proof prop r

@[zify_simps] lemma nat_cast_eq (a b : ℕ) : a = b ↔ (a : ℤ) = (b : ℤ) := Int.ofNat_inj.symm
@[zify_simps] lemma nat_cast_le (a b : ℕ) : a ≤ b ↔ (a : ℤ) ≤ (b : ℤ) := Int.ofNat_le.symm
@[zify_simps] lemma nat_cast_lt (a b : ℕ) : a < b ↔ (a : ℤ) < (b : ℤ) := Int.ofNat_lt.symm
@[zify_simps] lemma nat_cast_ne (a b : ℕ) : a ≠ b ↔ (a : ℤ) ≠ (b : ℤ) := by
  simp only [ne_eq, Int.cast_eq_cast_iff_Nat]
@[zify_simps] lemma nat_cast_dvd (a b : ℕ) : a ∣ b ↔ (a : ℤ) ∣ (b : ℤ) := Int.ofNat_dvd.symm
-- TODO: is it worth adding lemmas for Prime and Coprime as well?
-- Doing so in this file would require adding imports.
