/-
Copyright (c) 2023 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/

import Mathlib.Data.Rat.NNRat
import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# Binomial semirings and binomial rings

In this file we introduce binomial semirings and binomial rings, together with related functions
like binomial coefficients.

According to our main reference [Elliott] (which lists many equivalent conditions), a binomial ring
is a torsion-free commutative ring R such that for any x ∈ R and any k ∈ ℕ, the product
x(x-1)⋯(x-k+1) ∈ (k!)R.  The torsion-free condition lets us divide by k! unambiguously, so we get
uniquely defined binomial coefficients.

The defining condition doesn't require commutativity, and we get a theory with essentially the same
power by replacing subtraction with addition.  Thus, we consider a semiring R in which
multiplication by factorials is injective, and demand that for all x ∈ R and any k ∈ ℕ,
k! | x(x+1)⋯(x+(k-1)).
The quotient is called "multichoose r k", following the convention given for natural numbers.

## Main results

none yet

## References

J. Elliott, `Binomial rings, integer-valued polynomials, and λ-rings` J. Pure Appl. Alg. 207 (2006)
165--185.
-/

namespace Ring

universe u

variable {R:Type u}

/-- pochEval directly evaluates the n-th Pochhammer polynomial at an element r. -/
def pochEval [Semiring R] (r:R) : ℕ → R
  | 0 => 1
  | (k + 1) => (r+k) * (pochEval r k)

theorem pochEval_zero [Semiring R] (r : R) :
  pochEval r 0 = 1 := rfl

theorem pochEval_succ [Semiring R] (r : R) (k : ℕ) :
  pochEval r (k.succ) = (r + k) * (pochEval r k) := by rfl

theorem pochEval_cast [Semiring R] (n : ℕ) : ∀ (k : ℕ), pochEval (n:R) k = (pochEval n k)
| 0 => by rw [pochEval_zero, pochEval_zero, Nat.cast_one]
| (k+1) => by
  rw [pochEval_succ, pochEval_succ, Nat.cast_mul, pochEval_cast n k, Nat.cast_add]
  norm_cast

theorem mem_comm_translate [Semiring R] (r s: R) (n : ℕ) (h: Commute r s) : Commute r (s+n) := by
  refine Commute.add_right h (Nat.commute_cast r n)

theorem translate_comm_mem [Semiring R] (r s: R) (n : ℕ) (h: Commute r s) : Commute (r+n) s := by
  refine Commute.add_left h (Nat.cast_commute n s)

theorem translates_comm [Semiring R] (r s: R) (k n : ℕ) (h: Commute r s): Commute (r+k) (s+n) := by
  refine Commute.add_right ?_ ?_
  refine translate_comm_mem r s k h
  exact Nat.commute_cast (r+k) n

theorem translate_comm_pochEval [Semiring R] (r s:R) (k : ℕ) (h: Commute r s) : ∀ (n:ℕ),
  Commute (r+k) (pochEval s n)
  | 0 => by
    rw [pochEval_zero]
    exact Commute.one_right (r + ↑k)
  | (n+1) => by
    rw [pochEval_succ]
    refine Commute.mul_right ?_ ?_
    refine translates_comm r s k n h
    exact translate_comm_pochEval r s k h n

theorem pochEval_eq_pochhammer_eval [Semiring R] (r:R) :
  ∀ (k:ℕ), pochEval r k = Polynomial.eval r (pochhammer R k)
  | 0 => by rw [pochhammer_zero, Polynomial.eval_one, pochEval_zero]
  | (k + 1) => by
    rw [pochhammer_succ_eval, ← pochEval_eq_pochhammer_eval r k, pochEval_succ,
      translate_comm_pochEval]
    rfl

theorem pochEval_mul [Semiring R] (r:R) (n : ℕ) : ∀ (k:ℕ),
  pochEval r (n + k) = pochEval (r + n) k * pochEval r n
| 0=> by rw [add_zero, pochEval_zero, one_mul]
| (k+1) => by
  rw [← add_assoc, pochEval_succ, pochEval_mul r n k, pochEval_succ, mul_assoc, Nat.cast_add,
    add_assoc]

/-- A semiring is binomial if multiplication by factorials is injective and pochhammer evaluations
are divisible by the corresponding factorial. -/
class BinomialSemiring (R: Type u) extends Semiring R where
  /-- Multiplication by factorials is injective -/
  inj_smul_factorial : ∀ (n:ℕ) (r s: R), n.factorial * r = n.factorial * s → r = s
  /-- The multichoose function exists -/
  multichoose : R → ℕ → R
  /-- Defining property: multichoose r n is the quotient of pochhammer n (evaluated at r) by n! -/
  factorial_mul_multichoose : ∀ (r:R) (n : ℕ), n.factorial * multichoose r n = pochEval r n

theorem inj_smul_factorial [BinomialSemiring R] :  ∀ (n:ℕ) (r s: R),
  n.factorial * r = n.factorial * s → r = s := by
  exact BinomialSemiring.inj_smul_factorial

theorem eq_of_mul_eq_mul_factorial [BinomialSemiring R] {r s: R} (n:ℕ)
  (h:n.factorial*r = n.factorial*s) : r = s := by
  exact inj_smul_factorial n r s h

/-- This is a generalization of the combinatorial multichoose function, given by choosing with
replacement. -/
def multichoose [BinomialSemiring R] : R → ℕ → R :=
  λ r n => BinomialSemiring.multichoose r n

theorem factorial_mul_multichoose_eq_pochEval [BinomialSemiring R] {r: R} (n:ℕ) :
  n.factorial * multichoose r n = pochEval r n :=
  BinomialSemiring.factorial_mul_multichoose r n

end Ring
