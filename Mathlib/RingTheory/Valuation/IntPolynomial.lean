/-
Copyright (c) 2024 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-!
# Polynomials over subrings.

Given a field `K` with a subring `R`, in this file we construct a map from polynomials in `K[X]`
with coefficients in `R` to `R[X]`. We provide several lemmas to deal with
coefficients, degree, and evaluation of `intPolynomial`.
This is useful when dealing with integral elements in an extension of fields.

# Main Definitions
* `Valuation.intPolynomial` : given a polynomial in `K[X]` with coefficients in a field `K` with a
  subring `R` such that all coefficients belong to `R`, `intPolynomial R ` is the
  corresponding polynomial in `R[X]`.
-/

variable {K : Type*} [Field K] (R : Subring K)

open Polynomial

open scoped Polynomial

/-- Given a polynomial in `K[X]` such that all coefficients belong to the subring `R`,
  `intPolynomial` is the corresponding polynomial in `R[X]`. -/
def intPolynomial {P : K[X]} (hP : ∀ n : ℕ, P.coeff n ∈ R) : R[X]
    where toFinsupp :=
  { support := P.support
    toFun := fun n => ⟨P.coeff n, hP n⟩
    mem_support_toFun := fun n => by
      rw [ne_eq, ← Subring.coe_eq_zero_iff, mem_support_iff] }

namespace intPolynomial

variable {P : K[X]} (hP : ∀ n : ℕ, P.coeff n ∈ R)

theorem coeff_eq  (n : ℕ) : ↑((intPolynomial R hP).coeff n) = P.coeff n := rfl

theorem leadingCoeff_eq : ↑(intPolynomial R hP).leadingCoeff = P.leadingCoeff := rfl

theorem monic_iff : (intPolynomial R hP).Monic ↔ P.Monic := by
  rw [Monic, Monic, ← leadingCoeff_eq, OneMemClass.coe_eq_one]

theorem natDegree : (intPolynomial R hP).natDegree = P.natDegree := rfl

variable {L : Type*} [Field L] [Algebra K L]

theorem eval₂_eq (x : L) :
    eval₂ (algebraMap R L) x (intPolynomial R hP) = aeval x P := by
  rw [aeval_eq_sum_range, eval₂_eq_sum_range]
  exact Finset.sum_congr rfl (fun n _ => by rw [Algebra.smul_def]; rfl)

end intPolynomial
