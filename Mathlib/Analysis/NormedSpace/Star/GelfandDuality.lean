/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Reeased under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux

! This file was ported from Lean 3 source module analysis.normed_space.star.gelfand_duality
! leanprover-community/mathlib commit e65771194f9e923a70dfb49b6ca7be6e400d8b6f
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Analysis.NormedSpace.Star.Spectrum
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.NormedSpace.Algebra
import Mathlib.Topology.ContinuousFunction.Units
import Mathlib.Topology.ContinuousFunction.Compact
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.ContinuousFunction.StoneWeierstrass

/-!
# Gelfand Duality

The `gelfandTransform` is an algebra homomorphism from a topological `𝕜`-algebra `A` to
`C(character_space 𝕜 A, 𝕜)`. In the case where `A` is a commutative complex Banach algebra, then
the Gelfand transform is actually spectrum-preserving (`spectrum.gelfandTransform_eq`). Moreover,
when `A` is a commutative C⋆-algebra over `ℂ`, then the Gelfand transform is a surjective isometry,
and even an equivalence between C⋆-algebras.

## Main definitions

* `Ideal.toCharacterSpace` : constructs an element of the character space from a maximal ideal in
  a commutative complex Banach algebra
* `WeakDual.CharacterSpace.compContinuousMap`: The functorial map taking `ψ : A →⋆ₐ[ℂ] B` to a
  continuous function `characterSpace ℂ B → characterSpace ℂ A` given by pre-composition with `ψ`.

## Main statements

* `spectrum.gelfandTransform_eq` : the Gelfand transform is spectrum-preserving when the algebra is
  a commutative complex Banach algebra.
* `gelfandTransform_isometry` : the Gelfand transform is an isometry when the algebra is a
  commutative (unital) C⋆-algebra over `ℂ`.
* `gelfandTransform_bijective` : the Gelfand transform is bijective when the algebra is a
  commutative (unital) C⋆-algebra over `ℂ`.

## TODO

* After `StarAlgEquiv` is defined, realize `gelfandTransform` as a `StarAlgEquiv`.
* Prove that if `A` is the unital C⋆-algebra over `ℂ` generated by a fixed normal element `x` in
  a larger C⋆-algebra `B`, then `characterSpace ℂ A` is homeomorphic to `spectrum ℂ x`.
* From the previous result, construct the **continuous functional calculus**.
* Show that if `X` is a compact Hausdorff space, then `X` is (canonically) homeomorphic to
  `characterSpace ℂ C(X, ℂ)`.
* Conclude using the previous fact that the functors `C(⬝, ℂ)` and `characterSpace ℂ ⬝` along with
  the canonical homeomorphisms described above constitute a natural contravariant equivalence of
  the categories of compact Hausdorff spaces (with continuous maps) and commutative unital
  C⋆-algebras (with unital ⋆-algebra homomoprhisms); this is known as **Gelfand duality**.

## Tags

Gelfand transform, character space, C⋆-algebra
-/


open WeakDual

open scoped NNReal

section ComplexBanachAlgebra

open Ideal

variable {A : Type _} [NormedCommRing A] [NormedAlgebra ℂ A] [CompleteSpace A] (I : Ideal A)
  [Ideal.IsMaximal I]

/-- Every maximal ideal in a commutative complex Banach algebra gives rise to a character on that
algebra. In particular, the character, which may be identified as an algebra homomorphism due to
`WeakDual.CharacterSpace.equivAlgHom`, is given by the composition of the quotient map and
the Gelfand-Mazur isomorphism `NormedRing.algEquivComplexOfComplete`. -/
noncomputable def Ideal.toCharacterSpace : characterSpace ℂ A :=
  CharacterSpace.equivAlgHom.symm <|
    ((NormedRing.algEquivComplexOfComplete
      (letI := Quotient.field I; isUnit_iff_ne_zero (G₀ := A ⧸ I))).symm : A ⧸ I →ₐ[ℂ] ℂ).comp <|
    Quotient.mkₐ ℂ I
#align ideal.to_character_space Ideal.toCharacterSpace

theorem Ideal.toCharacterSpace_apply_eq_zero_of_mem {a : A} (ha : a ∈ I) :
    I.toCharacterSpace a = 0 := by
  unfold Ideal.toCharacterSpace
  simp only [CharacterSpace.equivAlgHom_symm_coe, AlgHom.coe_comp, AlgHom.coe_coe,
    Quotient.mkₐ_eq_mk, Function.comp_apply, NormedRing.algEquivComplexOfComplete_symm_apply]
  simp_rw [Quotient.eq_zero_iff_mem.mpr ha, spectrum.zero_eq]
  exact Set.eq_of_mem_singleton (Set.singleton_nonempty (0 : ℂ)).some_mem
#align ideal.to_character_space_apply_eq_zero_of_mem Ideal.toCharacterSpace_apply_eq_zero_of_mem

/-- If `a : A` is not a unit, then some character takes the value zero at `a`. This is equivlaent
to `gelfandTransform ℂ A a` takes the value zero at some character. -/
theorem WeakDual.CharacterSpace.exists_apply_eq_zero {a : A} (ha : ¬IsUnit a) :
    ∃ f : characterSpace ℂ A, f a = 0 := by
  obtain ⟨M, hM, haM⟩ := (span {a}).exists_le_maximal (span_singleton_ne_top ha)
  exact
    ⟨M.toCharacterSpace,
      M.toCharacterSpace_apply_eq_zero_of_mem
        (haM (mem_span_singleton.mpr ⟨1, (mul_one a).symm⟩))⟩
#align weak_dual.character_space.exists_apply_eq_zero WeakDual.CharacterSpace.exists_apply_eq_zero

theorem WeakDual.CharacterSpace.mem_spectrum_iff_exists {a : A} {z : ℂ} :
    z ∈ spectrum ℂ a ↔ ∃ f : characterSpace ℂ A, f a = z := by
  refine' ⟨fun hz => _, _⟩
  · obtain ⟨f, hf⟩ := WeakDual.CharacterSpace.exists_apply_eq_zero hz
    simp only [map_sub, sub_eq_zero, AlgHomClass.commutes, Algebra.id.map_eq_id,
      RingHom.id_apply] at hf
    refine ⟨f, ?_⟩
    rw [AlgHomClass.commutes, Algebra.id.map_eq_id, RingHom.id_apply] at hf
    exact hf.symm
  · rintro ⟨f, rfl⟩
    exact AlgHom.apply_mem_spectrum f a
#align weak_dual.character_space.mem_spectrum_iff_exists WeakDual.CharacterSpace.mem_spectrum_iff_exists

/-- The Gelfand transform is spectrum-preserving. -/
theorem spectrum.gelfandTransform_eq (a : A) :
    spectrum ℂ (gelfandTransform ℂ A a) = spectrum ℂ a := by
  ext z
  rw [ContinuousMap.spectrum_eq_range, WeakDual.CharacterSpace.mem_spectrum_iff_exists]
  exact Iff.rfl
#align spectrum.gelfand_transform_eq spectrum.gelfandTransform_eq

instance [Nontrivial A] : Nonempty (characterSpace ℂ A) :=
  ⟨Classical.choose <|
      WeakDual.CharacterSpace.exists_apply_eq_zero <| zero_mem_nonunits.2 zero_ne_one⟩

end ComplexBanachAlgebra

section ComplexCstarAlgebra

variable {A : Type _} [NormedCommRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

variable [StarRing A] [CstarRing A] [StarModule ℂ A]

theorem gelfandTransform_map_star (a : A) :
    gelfandTransform ℂ A (star a) = star (gelfandTransform ℂ A a) :=
  ContinuousMap.ext fun φ => map_star φ a
#align gelfand_transform_map_star gelfandTransform_map_star

variable (A)

/-- The Gelfand transform is an isometry when the algebra is a C⋆-algebra over `ℂ`. -/
theorem gelfandTransform_isometry : Isometry (gelfandTransform ℂ A) := by
  nontriviality A
  refine' AddMonoidHomClass.isometry_of_norm (gelfandTransform ℂ A) fun a => _
  /- By `spectrum.gelfandTransform_eq`, the spectra of `star a * a` and its
    `gelfandTransform` coincide. Therefore, so do their spectral radii, and since they are
    self-adjoint, so also do their norms. Applying the C⋆-property of the norm and taking square
    roots shows that the norm is preserved. -/
  have : spectralRadius ℂ (gelfandTransform ℂ A (star a * a)) = spectralRadius ℂ (star a * a) := by
    unfold spectralRadius; rw [spectrum.gelfandTransform_eq]
  rw [map_mul, (IsSelfAdjoint.star_mul_self _).spectralRadius_eq_nnnorm, gelfandTransform_map_star,
    (IsSelfAdjoint.star_mul_self (gelfandTransform ℂ A a)).spectralRadius_eq_nnnorm] at this
  simp only [ENNReal.coe_eq_coe, CstarRing.nnnorm_star_mul_self, ← sq] at this
  simpa only [Function.comp_apply, NNReal.sqrt_sq] using
    congr_arg (((↑) : ℝ≥0 → ℝ) ∘ ⇑NNReal.sqrt) this
#align gelfand_transform_isometry gelfandTransform_isometry

/-- The Gelfand transform is bijective when the algebra is a C⋆-algebra over `ℂ`. -/
theorem gelfandTransform_bijective : Function.Bijective (gelfandTransform ℂ A) := by
  refine' ⟨(gelfandTransform_isometry A).injective, _⟩
  suffices (gelfandTransform ℂ A).range = ⊤ by
    exact fun x => ((gelfandTransform ℂ A).mem_range).mp (this.symm ▸ Algebra.mem_top)
  /- Because the `gelfandTransform ℂ A` is an isometry, it has closed range, and so by the
    Stone-Weierstrass theorem, it suffices to show that the image of the Gelfand transform separates
    points in `C(characterSpace ℂ A, ℂ)` and is closed under `star`. -/
  have h : (gelfandTransform ℂ A).range.topologicalClosure = (gelfandTransform ℂ A).range :=
    le_antisymm
      (Subalgebra.topologicalClosure_minimal _ le_rfl
        (gelfandTransform_isometry A).closedEmbedding.closed_range)
      (Subalgebra.le_topologicalClosure _)
  refine' h ▸ ContinuousMap.subalgebra_isROrC_topologicalClosure_eq_top_of_separatesPoints
    _ (fun _ _ => _) fun f hf => _
  /- Separating points just means that elements of the `characterSpace` which agree at all points
    of `A` are the same functional, which is just extensionality. -/
  · contrapose!
    exact fun h => Subtype.ext (ContinuousLinearMap.ext fun a =>
      h (gelfandTransform ℂ A a) ⟨gelfandTransform ℂ A a, ⟨a, rfl⟩, rfl⟩)
  /- If `f = gelfandTransform ℂ A a`, then `star f` is also in the range of `gelfandTransform ℂ A`
    using the argument `star a`. The key lemma below may be hard to spot; it's `map_star` coming
    from `WeakDual.Complex.instStarHomClass`, which is a nontrivial result. -/
  · obtain ⟨f, ⟨a, rfl⟩, rfl⟩ := Subalgebra.mem_map.mp hf
    refine' ⟨star a, ContinuousMap.ext fun ψ => _⟩
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, gelfandTransform_apply_apply,
      AlgEquiv.toAlgHom_eq_coe, AlgHom.compLeftContinuous_apply_apply, AlgHom.coe_coe,
      IsROrC.conjAe_coe, map_star, starRingEnd_apply]
#align gelfand_transform_bijective gelfandTransform_bijective

/-- The Gelfand transform as a `StarAlgEquiv` between a commutative unital C⋆-algebra over `ℂ`
and the continuous functions on its `characterSpace`. -/
@[simps!]
noncomputable def gelfandStarTransform : A ≃⋆ₐ[ℂ] C(characterSpace ℂ A, ℂ) :=
  StarAlgEquiv.ofBijective
    (show A →⋆ₐ[ℂ] C(characterSpace ℂ A, ℂ) from
      { gelfandTransform ℂ A with map_star' := fun x => gelfandTransform_map_star x })
    (gelfandTransform_bijective A)
#align gelfand_star_transform gelfandStarTransform

end ComplexCstarAlgebra

section Functoriality

namespace WeakDual

namespace CharacterSpace

variable {A B C : Type _}

variable [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] [StarRing A]

variable [NormedRing B] [NormedAlgebra ℂ B] [CompleteSpace B] [StarRing B]

variable [NormedRing C] [NormedAlgebra ℂ C] [CompleteSpace C] [StarRing C]

/-- The functorial map taking `ψ : A →⋆ₐ[ℂ] B` to a continuous function
`characterSpace ℂ B → characterSpace ℂ A` obtained by pre-composition with `ψ`. -/
@[simps]
noncomputable def compContinuousMap (ψ : A →⋆ₐ[ℂ] B) : C(characterSpace ℂ B, characterSpace ℂ A)
    where
  toFun φ := equivAlgHom.symm ((equivAlgHom φ).comp ψ.toAlgHom)
  continuous_toFun :=
    Continuous.subtype_mk
      (continuous_of_continuous_eval fun a => map_continuous <| gelfandTransform ℂ B (ψ a)) _
#align weak_dual.character_space.comp_continuous_map WeakDual.CharacterSpace.compContinuousMap

variable (A)

/-- `WeakDual.CharacterSpace.compContinuousMap` sends the identity to the identity. -/
@[simp]
theorem compContinuousMap_id :
    compContinuousMap (StarAlgHom.id ℂ A) = ContinuousMap.id (characterSpace ℂ A) :=
  ContinuousMap.ext fun _a => ext fun _x => rfl
#align weak_dual.character_space.comp_continuous_map_id WeakDual.CharacterSpace.compContinuousMap_id

variable {A}

/-- `WeakDual.CharacterSpace.compContinuousMap` is functorial. -/
@[simp]
theorem compContinuousMap_comp (ψ₂ : B →⋆ₐ[ℂ] C) (ψ₁ : A →⋆ₐ[ℂ] B) :
    compContinuousMap (ψ₂.comp ψ₁) = (compContinuousMap ψ₁).comp (compContinuousMap ψ₂) :=
  ContinuousMap.ext fun _a => ext fun _x => rfl
#align weak_dual.character_space.comp_continuous_map_comp WeakDual.CharacterSpace.compContinuousMap_comp

end CharacterSpace

end WeakDual

end Functoriality
