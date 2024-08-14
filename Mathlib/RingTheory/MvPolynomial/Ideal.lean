/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.MonoidAlgebra.Ideal
import Mathlib.Algebra.MvPolynomial.Division

/-!
# Lemmas about ideals of `MvPolynomial`

Notably this contains results about monomial ideals.

## Main results

* `MvPolynomial.mem_ideal_span_monomial_image`
* `MvPolynomial.mem_ideal_span_X_image`
-/


variable {σ R : Type*}

namespace MvPolynomial

variable [CommSemiring R]

/-- `x` is in a monomial ideal generated by `s` iff every element of its support dominates one of
the generators. Note that `si ≤ xi` is analogous to saying that the monomial corresponding to `si`
divides the monomial corresponding to `xi`. -/
theorem mem_ideal_span_monomial_image {x : MvPolynomial σ R} {s : Set (σ →₀ ℕ)} :
    x ∈ Ideal.span ((fun s => monomial s (1 : R)) '' s) ↔ ∀ xi ∈ x.support, ∃ si ∈ s, si ≤ xi := by
  refine AddMonoidAlgebra.mem_ideal_span_of'_image.trans ?_
  simp_rw [le_iff_exists_add, add_comm]
  rfl

theorem mem_ideal_span_monomial_image_iff_dvd {x : MvPolynomial σ R} {s : Set (σ →₀ ℕ)} :
    x ∈ Ideal.span ((fun s => monomial s (1 : R)) '' s) ↔
      ∀ xi ∈ x.support, ∃ si ∈ s, monomial si 1 ∣ monomial xi (x.coeff xi) := by
  refine mem_ideal_span_monomial_image.trans (forall₂_congr fun xi hxi => ?_)
  simp_rw [monomial_dvd_monomial, one_dvd, and_true_iff, mem_support_iff.mp hxi, false_or_iff]

/-- `x` is in a monomial ideal generated by variables `X` iff every element of its support
has a component in `s`. -/
theorem mem_ideal_span_X_image {x : MvPolynomial σ R} {s : Set σ} :
    x ∈ Ideal.span (MvPolynomial.X '' s : Set (MvPolynomial σ R)) ↔
      ∀ m ∈ x.support, ∃ i ∈ s, (m : σ →₀ ℕ) i ≠ 0 := by
  have := @mem_ideal_span_monomial_image σ R _ x ((fun i => Finsupp.single i 1) '' s)
  rw [Set.image_image] at this
  refine this.trans ?_
  simp [Nat.one_le_iff_ne_zero]

/-- If a set `A` is contained in the span of another `B` then the span of `A` is also contained. -/
lemma sub_span_span_sub {A B : Set (MvPolynomial σ R)} (h : A ⊆ Ideal.span B) :
    SetLike.coe (Ideal.span A) ⊆ Ideal.span B := by
  simp only [SetLike.coe_subset_coe, Ideal.span_le.mpr h]

/-- Spans of two sets `A`, `B` are equal if and only if each is contained in the span of the
other -/
lemma span_eq_iff_basis_sub (A B : Set (MvPolynomial σ R)) :
    Ideal.span A = Ideal.span B ↔ A ⊆ Ideal.span B ∧ B ⊆ Ideal.span A := by
  constructor
  · intro h
    constructor
    · simpa [← h] using Ideal.subset_span
    · simpa [h] using Ideal.subset_span
  · intro ⟨hA, hB⟩
    simpa [← SetLike.coe_set_eq, Set.Subset.antisymm_iff] using
    ⟨sub_span_span_sub hA, sub_span_span_sub hB⟩

/-- If an element is a member of the basis of a span, it is in the span. -/
lemma mem_basis_mem_span {x : MvPolynomial σ R} {A : Set (MvPolynomial σ R)} (h : x ∈ A) :
    x ∈ Ideal.span A := by
  apply Ideal.subset_span
  simp_all only

variable [Nontrivial R]

/-- If a monomial `m` is contained in the span of a basis of monomials, there must be an
element of the basis dividing `m`. -/
lemma mem_span_exists_dvd_mem_basis {S : Set (σ →₀ ℕ)} (s : σ →₀ ℕ)
    (h : monomial s 1 ∈ Ideal.span ((fun s ↦ monomial s (1 : R)) '' S)) :
    ∃ i ∈ S, monomial i (1 : R) ∣ monomial s 1 := by
 classical
 rcases mem_ideal_span_monomial_image_iff_dvd.1 h s (by
  simp only [support_monomial, if_neg one_ne_zero, Finset.mem_singleton_self]) with ⟨j, hS, hj⟩
 use j, hS
 simpa [coeff_monomial, if_pos] using hj


end MvPolynomial
