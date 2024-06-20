/-
Copyright (c) 2023 Gareth Ma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gareth Ma
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Lucas's theorem

This file contains a proof of [Lucas's theorem](https://www.wikiwand.com/en/Lucas%27s_theorem) about
binomial coefficients, which says that for primes `p`, `n` choose `k` is congruent to product of
`n_i` choose `k_i` modulo `p`, where `n_i` and `k_i` are the base-`p` digits of `n` and `k`,
respectively.

## Main statements

* `lucas_theorem''`: the binomial coefficient `n choose k` is congruent to the
product of `n_i choose k_i` modulo `p`, where `n_i` and `k_i` are the base-`p`
digits of `n` and `k`, respectively.
-/

open Finset hiding choose

open Nat BigOperators Polynomial

namespace Choose

variable {n k p : ℕ} [Fact p.Prime]

/-- **Lucas's Theorem**: For primes `p`, `choose n k` is congruent to `choose (n % p) (k % p) *
choose (n / p) (k / p)` modulo `p`. -/
theorem lucas_theorem :choose n k ≡ choose (n % p) (k % p) * choose (n / p) (k / p) [ZMOD p] := by
  have decompose : ((X : (ZMod p)[X]) + 1) ^ n = (X + 1) ^ (n % p) * (X ^ p + 1) ^ (n / p) := by
    simpa using add_pow_eq_add_pow_mod_mul_pow_add_pow_div _ (X : (ZMod p)[X]) 1
  simp only [← ZMod.intCast_eq_intCast_iff, Int.cast_mul, Int.cast_ofNat,
    ← coeff_X_add_one_pow _ n k, ← eq_intCast (Int.castRingHom (ZMod p)), ← coeff_map,
    Polynomial.map_pow, Polynomial.map_add, Polynomial.map_one, map_X, decompose]
  simp only [add_pow, one_pow, mul_one, ← pow_mul, sum_mul_sum]
  conv_lhs =>
    enter [1, 2, k, 2, k']
    rw [← mul_assoc, mul_right_comm _ _ (X ^ (p * k')), ← pow_add, mul_assoc, ← cast_mul]
  have h_iff : ∀ x ∈ range (n % p + 1) ×ˢ range (n / p + 1),
      k = x.1 + p * x.2 ↔ (k % p, k / p) = x := by
    intro ⟨x₁, x₂⟩ hx
    rw [Prod.mk.injEq]
    constructor <;> intro h
    · simp only [mem_product, mem_range] at hx
      have h' : x₁ < p := lt_of_lt_of_le hx.left $ mod_lt _ Fin.size_pos'
      rw [h, add_mul_mod_self_left, add_mul_div_left _ _ Fin.size_pos', eq_comm (b := x₂)]
      exact ⟨mod_eq_of_lt h', self_eq_add_left.mpr (div_eq_of_lt h')⟩
    · rw [← h.left, ← h.right, mod_add_div]
  simp only [finset_sum_coeff, coeff_mul_natCast, coeff_X_pow, ite_mul, zero_mul, ← cast_mul]
  rw [← sum_product', sum_congr rfl (fun a ha ↦ if_congr (h_iff a ha) rfl rfl), sum_ite_eq]
  split_ifs with h
  · simp
  · rw [mem_product, mem_range, mem_range, not_and_or, lt_succ, not_le, not_lt] at h
    cases h <;> simp [choose_eq_zero_of_lt (by tauto)]

/-- **Lucas's Theorem**: For primes `p`, `choose n k` is congruent to the product of
`choose (⌊n / p ^ i⌋ % p) (⌊k / p ^ i⌋ % p)` over i < a, multiplied by
`choose (⌊n / p ^ a⌋) (⌊k / p ^ a⌋)`, modulo `p`. -/
theorem lucas_theorem' (a : ℕ) :
    choose n k ≡ choose (n / p ^ a) (k / p ^ a) *
      ∏ i in range a, choose (n / p ^ i % p) (k / p ^ i % p) [ZMOD p] :=
  match a with
  | Nat.zero => by simp
  | Nat.succ a => (lucas_theorem' a).trans <| by
    rw [prod_range_succ, cast_mul, ← mul_assoc, mul_right_comm]
    gcongr
    apply lucas_theorem.trans
    simp_rw [pow_succ, Nat.div_div_eq_div_mul, mul_comm]
    rfl

/-- **Lucas's Theorem**: For primes `p`, `choose n k` is congruent to the product of
`choose (⌊n / p ^ i⌋ % p) (⌊k / p ^ i⌋ % p)` over `i` modulo `p`. -/
theorem lucas_theorem'' {a : ℕ} (ha₁ : n < p ^ a) (ha₂ : k < p ^ a) :
    choose n k ≡ ∏ i in range a, choose (n / p ^ i % p) (k / p ^ i % p) [ZMOD p] := by
  apply (lucas_theorem' a).trans
  simp_rw [(Nat.div_eq_zero_iff $ by omega).mpr ha₁, (Nat.div_eq_zero_iff $ by omega).mpr ha₂,
    choose, cast_one, one_mul, cast_prod]
  rfl
