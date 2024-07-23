/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/

import Mathlib.Init.Order.Defs
import Mathlib.Data.Int.Notation
import Mathlib.Data.Nat.Notation

/-!
# Note about `Mathlib/Init/`
The files in `Mathlib/Init` are leftovers from the port from Mathlib3.
(They contain content moved from lean3 itself that Mathlib needed but was not moved to lean4.)

We intend to move all the content of these files out into the main `Mathlib` directory structure.
Contributions assisting with this are appreciated.

# The order relation on the integers
-/

open Nat

namespace Int

export private decNonneg from Init.Data.Int.Basic

theorem le.elim {a b : ℤ} (h : a ≤ b) {P : Prop} (h' : ∀ n : ℕ, a + ↑n = b → P) : P :=
  Exists.elim (le.dest h) h'

alias ⟨le_of_ofNat_le_ofNat, ofNat_le_ofNat_of_le⟩ := ofNat_le

theorem lt.elim {a b : ℤ} (h : a < b) {P : Prop} (h' : ∀ n : ℕ, a + ↑(Nat.succ n) = b → P) : P :=
  Exists.elim (lt.dest h) h'

alias ⟨lt_of_ofNat_lt_ofNat, ofNat_lt_ofNat_of_lt⟩ := ofNat_lt

instance instLinearOrder : LinearOrder ℤ where
  le := (·≤·)
  le_refl := Int.le_refl
  le_trans := @Int.le_trans
  le_antisymm := @Int.le_antisymm
  lt := (·<·)
  lt_iff_le_not_le := @Int.lt_iff_le_not_le
  le_total := Int.le_total
  decidableEq := by infer_instance
  decidableLE := by infer_instance
  decidableLT := by infer_instance

theorem neg_mul_eq_neg_mul_symm (a b : ℤ) : -a * b = -(a * b) := (Int.neg_mul_eq_neg_mul a b).symm

theorem mul_neg_eq_neg_mul_symm (a b : ℤ) : a * -b = -(a * b) := (Int.neg_mul_eq_mul_neg a b).symm

protected theorem eq_zero_or_eq_zero_of_mul_eq_zero {a b : ℤ} (h : a * b = 0) : a = 0 ∨ b = 0 :=
  match lt_trichotomy 0 a with
  | Or.inl hlt₁ =>
    match lt_trichotomy 0 b with
    | Or.inl hlt₂ => by
      have : 0 < a * b := Int.mul_pos hlt₁ hlt₂
      rw [h] at this
      exact absurd this (lt_irrefl _)
    | Or.inr (Or.inl heq₂) => Or.inr heq₂.symm
    | Or.inr (Or.inr hgt₂) => by
      have : 0 > a * b := Int.mul_neg_of_pos_of_neg hlt₁ hgt₂
      rw [h] at this
      exact absurd this (lt_irrefl _)
  | Or.inr (Or.inl heq₁) => Or.inl heq₁.symm
  | Or.inr (Or.inr hgt₁) =>
    match lt_trichotomy 0 b with
    | Or.inl hlt₂ => by
      have : 0 > a * b := Int.mul_neg_of_neg_of_pos hgt₁ hlt₂
      rw [h] at this
      exact absurd this (lt_irrefl _)
    | Or.inr (Or.inl heq₂) => Or.inr heq₂.symm
    | Or.inr (Or.inr hgt₂) => by
      have : 0 < a * b := Int.mul_pos_of_neg_of_neg hgt₁ hgt₂
      rw [h] at this
      exact absurd this (lt_irrefl _)

theorem nonneg_or_nonpos_of_mul_nonneg {a b : ℤ} : 0 ≤ a * b → 0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0 := by
  intro h
  by_cases ha : 0 ≤ a <;> by_cases hb : 0 ≤ b
  · exact .inl ⟨ha, hb⟩
  · refine .inr ⟨?_, le_of_not_le hb⟩
    obtain _ | _ := Int.mul_eq_zero.mp <|
      Int.le_antisymm (Int.mul_nonpos_of_nonneg_of_nonpos ha <| le_of_not_le hb) h
    all_goals omega
  · refine .inr ⟨le_of_not_le ha, ?_⟩
    obtain _ | _ := Int.mul_eq_zero.mp <|
      Int.le_antisymm (Int.mul_nonpos_of_nonpos_of_nonneg (le_of_not_le ha) hb) h
    all_goals omega
  · exact .inr ⟨le_of_not_ge ha, le_of_not_ge hb⟩

theorem mul_nonneg_of_nonneg_or_nonpos {a b : ℤ} : 0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0 → 0 ≤ a * b
  | .inl ⟨ha, hb⟩ => Int.mul_nonneg ha hb
  | .inr ⟨ha, hb⟩ => Int.mul_nonneg_of_nonpos_of_nonpos ha hb

protected theorem mul_nonneg_iff {a b : ℤ} : 0 ≤ a * b ↔ 0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0 :=
  ⟨nonneg_or_nonpos_of_mul_nonneg, mul_nonneg_of_nonneg_or_nonpos⟩
