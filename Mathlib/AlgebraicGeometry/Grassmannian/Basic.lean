/-
Copyright (c) 2024 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patricio Gallardo Candela, Yun Liu, Sophie Morel, David Swinarski, Weihong Xu
This contribution was created as part of the AIM workshop "Formalizing algebraic geometry" in
June 2024.
-/
import Mathlib.AlgebraicGeometry.Grassmannian.Lemmas
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!

# The Grassmannian scheme

The goal of this file is to define the Grassmannian scheme by gluing affine charts.
We fix a commutative ring `K`, a free `K`-module of finite type `V` and two natural numbers
`r` and `c`. The scheme we define should parametrize surjective `K`-linear maps
`V →ₗ[K] (Fin r → K)`, assuming that `V` is of rank `r + c`. We actually define the scheme
without assuming the condition on the rank of `V`, but it is empty unless the rank of `V` is
`r + c`.

Main definitions:
* `Grassmannian.glueData K V r c`: the `AlgebraicGeometry.Scheme.GlueData` defining the
Grassmannian scheme.
* `Grassmannian K V r c`: the Grassmannian scheme, defined as
`(Grassmannian.glueData K V r c).glued`.
* `Grassmannian.structMorphism K V r c`: the structural morphism from `Grassmannian K V r c`
to `Spec K`.

# Implementation

We use as index type for the charts the type `Basis (Fin (r + c)) K V` (so this is empty unless
`V` is free of rank `r + c`). All the charts are the same and equal to the affine space with
coordinates indexed by `Fin c × Fin r`, that is, to `Spec (MvPolynomial (Fin c × Fin r) K)`.
The idea is that, for `i` in `Basis (Fin (r + c)) K V`, the corresponding chart will
parametrize all surjective `K`-linear maps `φ : V →ₗ[K] (Fin r → K)` that become isomorphisms
when restricted to the `K`-submodule generated by the first `r` vectors of the basis `i`.
To get the point of the chart corresponding to `φ`, we take the matrix of `φ` in the basis `i` of
`V` and the canonical basis of `Fin r → K`, we divide it on the right by its top `r × r`
square submatrix (which is invertible by assumption), and we taken the botton `c × r`
submatrix.

This is almost the usual description of the Grassmannian by charts, with three differences:
* We consider the Grassmannian parametrizing `r`-dimensional quotients of `V` instead of
`r`-dimensional subspaces of `V`, because this is more natural when working over a general
ring (or scheme).
* In the usual description, we fix a basis of `V` and index the chart by its subsets `I` of
cardinality `r`. Here, to avoid making a choice, we instead index charts by the set of
bases of `V` and always choose the subset `I` to consist of the first `r` vectors.
* Instead of working with `FiniteDimensional.finrank K V - r`, which would cause technical
trouble because of the way subtraction works on `ℕ`, we introduce the codimension `c` as an
auxiliary variable, and our constructions are only interesting when `r + c` is equal to
`FiniteDimensional.finrank K V`.

## TODO

Describe the functor of points of the Grassmannian scheme. (We need more about quasi-coherent
sheaves in mathlib before we can do that.)
-/

open AlgebraicGeometry Scheme FiniteDimensional CategoryTheory Matrix

noncomputable section

universe u v w

variable (K V : Type u) [CommRing K] [AddCommGroup V] [Module K V]
variable (r c : ℕ)
variable {A : Type*} [CommRing A] [Algebra K A]

namespace Grassmannian

abbrev functions_chart := MvPolynomial (Fin c × Fin r) K

abbrev chart :=
  Spec (CommRingCat.of (MvPolynomial (Fin c × Fin r) K))

abbrev matrix_coord : Matrix (Fin (r + c)) (Fin r) (functions_chart K r c) :=
  Matrix.of
    (fun x y ↦
      if h : x < r then if x.1 = y.1 then 1 else 0
      else MvPolynomial.X (⟨x.1 - r, by have := x.2; rw [lt_iff_not_le, not_not] at h; omega⟩, y))

abbrev matrix_X : Matrix (Fin c) (Fin r) (functions_chart K r c) :=
  Matrix.of (fun p q ↦ MvPolynomial.X (p,q))

lemma matrix_coord_submatrix₁ :
    (matrix_coord K r c).submatrix (Fin.castLE (Nat.le_add_right r c)) id = 1 := by
  apply Matrix.ext; intro p q
  simp only [submatrix_apply, id_eq, of_apply, Fin.coe_castLE, Fin.is_lt, ↓reduceDite]
  by_cases h : p = q
  · simp only [h, ↓reduceIte, one_apply_eq]
  · simp only [ne_eq, h, not_false_eq_true, one_apply_ne, ite_eq_right_iff, one_ne_zero, imp_false]
    rw [← Fin.ext_iff]; intro h'; exfalso; exact h h'

lemma matrix_coord_submatrix₂ : (matrix_coord K r c).submatrix
    (fun i ↦ ⟨i.1 + r, by have := i.2; omega⟩ : Fin c → Fin (r + c)) id
    = matrix_X K r c := by
  apply Matrix.ext; intro p q
  simp only [submatrix_apply, id_eq, of_apply, add_lt_iff_neg_right, not_lt_zero', ↓reduceDite,
    add_tsub_cancel_right, Fin.eta]

variable {K V r c}

abbrev B (i j : Basis (Fin (r + c)) K V) := i.toMatrix j

variable (r c)

abbrev matrix (i j : Basis (Fin (r + c)) K V) :=
  (B j i).map (algebraMap K _) * matrix_coord K r c

abbrev matrix_F (i j : Basis (Fin (r + c)) K V) :
    Matrix (Fin r) (Fin r) (functions_chart K r c) :=
  Matrix.submatrix ((B j i).map (algebraMap K _) * matrix_coord K r c)
  (Fin.castLE (Nat.le_add_right r c)) id

abbrev matrix_G (i j : Basis (Fin (r + c)) K V) :
    Matrix (Fin c) (Fin r) (functions_chart K r c) :=
  Matrix.submatrix ((B j i).map (algebraMap K _) * matrix_coord K r c)
    (fun i ↦ ⟨i.1 + r, by have := i.2; omega⟩) id

lemma matrix_F_eq_id_of_diagonal (i : Basis (Fin (r + c)) K V) :
    matrix_F r c i i = 1 := by
  apply Matrix.ext; intro a b
  simp only [matrix_F, Basis.toMatrix_self, MvPolynomial.algebraMap_eq, map_zero, _root_.map_one,
    Matrix.map_one, Matrix.one_mul, submatrix_apply, id_eq, of_apply, Fin.coe_castLE, Fin.is_lt,
    ↓reduceDite]
  by_cases h : a = b
  · simp only [h, ↓reduceIte, one_apply_eq]
  · simp only [ne_eq, h, not_false_eq_true, one_apply_ne, ite_eq_right_iff]
    rw [← Fin.ext_iff]
    simp only [h, false_implies]

lemma matrix_G_eq_of_diagonal (i : Basis (Fin (r + c)) K V) :
    matrix_G r c i i = Matrix.of (fun p q ↦ MvPolynomial.X (p,q)) := by
  apply Matrix.ext; intro _ _
  simp only [matrix_G, Basis.toMatrix_self, MvPolynomial.algebraMap_eq, map_zero, _root_.map_one,
    Matrix.map_one, Matrix.one_mul, submatrix_apply, id_eq, of_apply, add_lt_iff_neg_right,
    not_lt_zero', ↓reduceDite, add_tsub_cancel_right, Fin.eta]

/-- If `i` and `j` are in the type indexing charts, this is the equation of the intersection of
the charts `U i` and `U j`, seen as a basic open subscheme of `U i`.
-/
def equation (i j : Basis (Fin (r + c)) K V) :
    (MvPolynomial ((Fin c) × Fin r) K) := (matrix_F r c i j).det

abbrev matrix_F' (i j : Basis (Fin (r + c)) K V) :=
  (algebraMap (MvPolynomial (Fin c × Fin r) K)
    (Localization.Away (equation r c i j))).mapMatrix (matrix_F r c i j)

abbrev matrix_G' (i j : Basis (Fin (r + c)) K V) :=
  (matrix_G r c i j).map
  (algebraMap (MvPolynomial (Fin c × Fin r) K) (Localization.Away (equation r c i j)))

abbrev matrix_X' (i j : Basis (Fin (r + c)) K V) :=
  (matrix_X K r c).map
  (algebraMap (MvPolynomial (Fin c × Fin r) K) (Localization.Away (equation r c i j)))

lemma matrix_F'_eq_id_of_diagonal (i : Basis (Fin (r + c)) K V) :
    matrix_F' r c i i = 1 := by
  simp only [matrix_F', matrix_F_eq_id_of_diagonal, _root_.map_one]

lemma matrix_G'_eq_X_of_diagonal (i : Basis (Fin (r + c)) K V) :
    matrix_G' r c i i = Matrix.of (fun p q ↦
    (algebraMap (MvPolynomial (Fin c × Fin r) K)
    (Localization.Away (equation r c i i)) (MvPolynomial.X (p,q)))) := by
  simp only [matrix_G', matrix_G_eq_of_diagonal]
  ext _ _
  simp only [map_apply, of_apply]

local instance isUnit_F' (i j : Basis (Fin (r + c)) K V) :
    IsUnit (matrix_F' r c i j) := by
    rw [Matrix.isUnit_iff_isUnit_det]
    rw [← RingHom.map_det]
    simp only [equation]
    refine isUnit_iff_exists_inv.mpr ?_
    existsi IsLocalization.Away.invSelf (matrix_F r c i j).det
    simp only [IsLocalization.Away.mul_invSelf]

lemma equation_eq_one_of_diagonal (i : Basis (Fin (r + c)) K V) :
    equation r c i i = 1 := by
  simp only [equation]
  rw [matrix_F_eq_id_of_diagonal]
  simp only [det_one]

abbrev open_immersion (i j : Basis (Fin (r + c)) K V) :=
  Spec.map (CommRingCat.ofHom (algebraMap (MvPolynomial ((Fin c) × Fin r) K)
    (Localization.Away (equation r c i j))))

abbrev transition_aux (i j : Basis (Fin (r + c)) K V) :
    functions_chart K r c →ₐ[K] Localization.Away (equation r c i j) :=
  {MvPolynomial.eval₂Hom (algebraMap K (Localization.Away (equation r c i j)))
  (fun pq ↦ ((matrix_G' r c i j) * (matrix_F' r c i j)⁻¹) pq.1 pq.2) with
    commutes' := by
      intro a
      simp only [RingHom.toMonoidHom_eq_coe, MvPolynomial.algebraMap_eq, OneHom.toFun_eq_coe,
        MonoidHom.toOneHom_coe, MonoidHom.coe_coe, MvPolynomial.eval₂Hom_C]}

lemma transition_aux_matrix_X (i j : Basis (Fin (r + c)) K V) :
    Matrix.map (matrix_X K r c) (transition_aux r c i j) =
    (matrix_G' r c i j) * (matrix_F' r c i j)⁻¹ := by
  conv_rhs => congr; change matrix_G' r c i j
  apply Matrix.ext; intro _ _
  simp only [AlgHom.coe_mk, RingHom.mapMatrix_apply, MvPolynomial.coe_eval₂Hom, map_apply,
      of_apply, MvPolynomial.eval₂_X]

lemma transition_aux_matrix_coord (i j : Basis (Fin (r + c)) K V) :
    Matrix.map (matrix_coord K r c) (transition_aux r c i j) =
    (matrix r c i j).map (algebraMap (MvPolynomial (Fin c × Fin r) K)
    (Localization.Away (equation r c i j))) * (matrix_F' r c i j)⁻¹ := by
  refine Matrix.eq_of_submatrix_eq (Fin.castLE (Nat.le_add_right r c))
    (fun i ↦ ⟨i.1 + r, by have := i.2; omega⟩ : Fin c → Fin (r + c))
    _ _ ?_ ?_ ?_
  · rw [Matrix.submatrix_mul _ _ (Fin.castLE (Nat.le_add_right r c)) id id Function.bijective_id,
      Matrix.submatrix_id_id, Matrix.submatrix_map, matrix_coord_submatrix₁]
    rw [Matrix.submatrix_map]
    conv_rhs => congr; change matrix_F' r c i j
    have := IsUnit.invertible (isUnit_F' r c i j)
    rw [Matrix.mul_inv_of_invertible]
    simp only [AlgHom.coe_mk, RingHom.mapMatrix_apply, MvPolynomial.coe_eval₂Hom,
      MvPolynomial.eval₂_zero, MvPolynomial.eval₂_one, Matrix.map_one]
  · rw [Matrix.submatrix_mul _ _ _ id id Function.bijective_id,
      Matrix.submatrix_id_id, Matrix.submatrix_map, matrix_coord_submatrix₂]
    rw [Matrix.submatrix_map]
    exact transition_aux_matrix_X r c _ _
  · intro i
    by_cases h : i.1 < r
    · left
      existsi ⟨i.1, h⟩
      simp only [Fin.castLE_mk, Fin.eta]
    · right
      existsi ⟨i - r, by have := i.2; omega⟩
      simp only; rw [Fin.ext_iff]
      rw [lt_iff_not_le, not_not] at h
      simp only [h, Nat.sub_add_cancel]

lemma transition_aux_matrix (i j k l : Basis (Fin (r + c)) K V) :
    Matrix.map (matrix r c k l) (transition_aux r c i j) =
    (B l k).map (algebraMap K (Localization.Away (equation r c i j))) *
    (B j i).map (algebraMap K (Localization.Away (equation r c i j))) *
    (matrix_coord K r c).map (algebraMap (MvPolynomial (Fin c × Fin r) K)
    (Localization.Away (equation r c i j))) * (matrix_F' r c i j)⁻¹ := by
  simp only [matrix]
  erw [RingHom.map_matrix_mul']; rw [Matrix.map_map]
  have : (transition_aux r c i j).toRingHom.toFun ∘ (algebraMap K (functions_chart K r c)) =
      algebraMap K _ := by
    ext _
    simp only [RingHom.mapMatrix_apply, RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe,
      MonoidHom.toOneHom_coe, MonoidHom.coe_coe, MvPolynomial.coe_eval₂Hom,
      MvPolynomial.algebraMap_eq, Function.comp_apply, MvPolynomial.eval₂_C]
  rw [this]
  conv_lhs => congr; rfl; erw [transition_aux_matrix_coord]
  simp only [matrix]
  conv_rhs => rw [Matrix.mul_assoc, Matrix.mul_assoc]
  congr 1
  conv_rhs => rw [← Matrix.mul_assoc]
  congr 1
  conv_lhs => rw [RingHom.map_matrix_mul']
  rfl

lemma transition_aux_F (i j k : Basis (Fin (r + c)) K V) :
    Matrix.map (matrix_F r c j k) (transition_aux r c i j) =
    (matrix_F r c i k).map (algebraMap (MvPolynomial (Fin c × Fin r) K)
    (Localization.Away (equation r c i j))) * (matrix_F' r c i j)⁻¹ := by
  simp only [matrix_F]
  rw [← Matrix.submatrix_map, transition_aux_matrix]
  erw [← RingHom.map_matrix_mul']; rw [Basis.toMatrix_mul_toMatrix k j i]
  rw [Matrix.submatrix_mul _ _ (e₁ := (Fin.castLE (Nat.le_add_right r c)))
    (e₂ := id (α := Fin r)) _ Function.bijective_id, Matrix.submatrix_id_id]
  congr 1
  rw [← Matrix.submatrix_map]
  conv_rhs => rw [RingHom.map_matrix_mul']
  rfl

lemma transition_aux_G (i j k : Basis (Fin (r + c)) K V) :
    Matrix.map (matrix_G r c j k) (transition_aux r c i j) =
    (matrix_G r c i k).map (algebraMap (MvPolynomial (Fin c × Fin r) K)
    (Localization.Away (equation r c i j))) * (matrix_F' r c i j)⁻¹ := by
  simp only [matrix_G]
  rw [← Matrix.submatrix_map, transition_aux_matrix]
  erw [← RingHom.map_matrix_mul']; rw [Basis.toMatrix_mul_toMatrix k j i]
  conv_lhs => rw [Matrix.submatrix_mul _ (matrix_F' r c i j)⁻¹ _ (e₂ := id (α := Fin r))
    (e₃ := id (α := Fin r)) Function.bijective_id, Matrix.submatrix_id_id]
  congr 1
  rw [← Matrix.submatrix_map]
  conv_rhs => rw [RingHom.map_matrix_mul']
  rfl

lemma transition_aux_equation (i j k : Basis (Fin (r + c)) K V) :
    transition_aux r c i j (equation r c j k) =
    algebraMap _ (Localization.Away (equation r c i j)) (equation r c i k) *
    IsLocalization.Away.invSelf (equation r c i j) := by
  simp only [equation]
  conv_lhs => erw [RingHom.map_det (transition_aux r c i j).toRingHom (matrix_F r c j k)]
              rw [RingHom.mapMatrix_apply]; erw [transition_aux_F]
              rw [Matrix.det_mul, det_nonsing_inv, matrix_F', ← RingHom.map_det,
                ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  congr 1
  rw [← one_mul (Ring.inverse _)]
  symm
  simp only [equation]
  rw [Ring.eq_mul_inverse_iff_mul_eq, mul_comm, IsLocalization.Away.mul_invSelf]
  exact Localization.Away.map_unit _ _

lemma transition_aux_F_flip (i j : Basis (Fin (r + c)) K V) :
    Matrix.map (matrix_F r c j i) (transition_aux r c i j) = (matrix_F' r c i j)⁻¹ := by
  rw [transition_aux_F, matrix_F_eq_id_of_diagonal]
  simp only [map_zero, _root_.map_one, Matrix.map_one, RingHom.mapMatrix_apply, one_mul]

lemma transition_aux_G_flip (i j : Basis (Fin (r + c)) K V) :
    Matrix.map (matrix_G r c j i) (transition_aux r c i j) =
    (matrix_X' r c i j) * (matrix_F' r c i j)⁻¹ := by
  rw [transition_aux_G, matrix_G_eq_of_diagonal]

lemma transition_aux_equation_flip (i j : Basis (Fin (r + c)) K V) :
    transition_aux r c i j (equation r c j i) = IsLocalization.Away.invSelf (equation r c i j) := by
  simp only [equation]
  conv_lhs => erw [RingHom.map_det (transition_aux r c i j).toRingHom (matrix_F r c j i)]
              rw [RingHom.mapMatrix_apply]; erw [transition_aux_F_flip]
              rw [det_nonsing_inv, matrix_F', ← RingHom.map_det]
  rw [← one_mul (Ring.inverse _)]
  symm
  simp only [equation]
  rw [Ring.eq_mul_inverse_iff_mul_eq, mul_comm, IsLocalization.Away.mul_invSelf]
  exact Localization.Away.map_unit _ _


lemma transition_aux_equation_isUnit (i j : Basis (Fin (r + c)) K V) :
    IsUnit ((transition_aux r c i j) (equation r c j i)) := by
  erw [transition_aux_equation_flip]
  exact IsLocalization.Away.invSelf_unit _ (equation r c i j)

abbrev transitionRingHom (i j : Basis (Fin (r + c)) K V) :
    Localization.Away (equation r c j i) →+* Localization.Away (equation r c i j) := by
  apply Localization.awayLift (r := equation r c j i) (transition_aux r c i j)
  exact transition_aux_equation_isUnit _ _ _ _

abbrev transition (i j : Basis (Fin (r + c)) K V) :
    Localization.Away (equation r c j i) →ₐ[K] Localization.Away (equation r c i j) :=
  {
   transitionRingHom r c i j with
   commutes' := by
     intro x
     dsimp
     rw [transitionRingHom]
     rw [IsScalarTower.algebraMap_apply _ (functions_chart K r c) _]
     rw [IsLocalization.Away.AwayMap.lift_eq]
     simp only [AlgHom.coe_ringHom_mk, RingHom.mapMatrix_apply, MvPolynomial.algebraMap_eq,
       MvPolynomial.eval₂Hom_C]
  }

lemma transition_F'_flip (i j : Basis (Fin (r + c)) K V) :
    Matrix.map (matrix_F' r c j i) (transition r c i j) = (matrix_F' r c i j)⁻¹ := by
  rw [transition, matrix_F', RingHom.mapMatrix_apply, Matrix.map_map]
  rw [← AlgHom.coe_toRingHom]
  rw [← RingHom.coe_comp]; erw [IsLocalization.Away.AwayMap.lift_comp]
  erw [transition_aux_F_flip]; erw [transition_aux_equation_flip]
  apply IsLocalization.Away.invSelf_unit

lemma transition_F'_inv_flip (i j : Basis (Fin (r + c)) K V) :
    Matrix.map (matrix_F' r c j i)⁻¹ (transition r c i j) = matrix_F' r c i j := by
  rw [← AlgHom.coe_toRingHom]
  rw [← RingHom.mapMatrix_apply, Matrix.nonsing_inv_eq_ring_inverse]
  erw [RingHom.map_inv (f := (transition r c i j).toRingHom.mapMatrix)
    (α := Matrix (Fin r) (Fin r) (Localization.Away (equation r c j i)))
    (β := Matrix (Fin r) (Fin r) (Localization.Away (equation r c i j)))]
  rw [RingHom.mapMatrix_apply]
  erw [transition_F'_flip]
  rw [← Matrix.nonsing_inv_eq_ring_inverse (matrix_F' r c i j)⁻¹, Matrix.nonsing_inv_nonsing_inv]
  rw [← Matrix.isUnit_iff_isUnit_det]; all_goals (exact isUnit_F' _ _ _ _)

lemma transition_G'_flip (i j : Basis (Fin (r + c)) K V) :
    Matrix.map (matrix_G' r c j i) (transition r c i j) =
    (matrix_X' r c i j) * (matrix_F' r c i j)⁻¹ := by
  rw [transition, matrix_G', Matrix.map_map]
  rw [← AlgHom.coe_toRingHom, ← RingHom.coe_comp]; erw [IsLocalization.Away.AwayMap.lift_comp]
  erw [transition_aux_G_flip]
  exact transition_aux_equation_isUnit _ _ _ _

lemma transition_transition (i j : Basis (Fin (r + c)) K V) :
    (transition r c i j).comp (transition r c j i) = AlgHom.id _ _ := by
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext (R := MvPolynomial (Fin c × Fin r) K)
    (M := Submonoid.powers (equation r c i j))
  simp only [AlgHom.id_toRingHom, RingHomCompTriple.comp_eq]
  rw [AlgHom.comp_toRingHom, RingHom.comp_assoc]
  conv_lhs => congr; rfl; rw [transition]; erw [IsLocalization.Away.AwayMap.lift_comp]; rfl;
              exact transition_aux_equation_isUnit _ _ _ _
  ext x
  · rw [← MvPolynomial.algebraMap_eq]
    rw [← AlgHom.comp_toRingHom]
    erw [AlgHom.comp_algebraMap]
    simp only [transition, AlgHom.coe_ringHom_mk, RingHom.mapMatrix_apply,
    MvPolynomial.comp_eval₂Hom, RingHom.coe_comp, MvPolynomial.coe_eval₂Hom, Function.comp_apply,
    MvPolynomial.eval₂_C]
    rw [← IsScalarTower.algebraMap_apply]
  · simp only [AlgHom.coe_ringHom_mk, RingHom.mapMatrix_apply, MvPolynomial.comp_eval₂Hom,
    MvPolynomial.eval₂Hom_X']
    change ((matrix_G' r c j i) * (matrix_F' r c j i)⁻¹).map (transition r c i j) x.1 x.2 = _
    erw [Matrix.map_mul, transition_F'_inv_flip, transition_G'_flip]
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul, Matrix.mul_one]
    simp only [map_apply, of_apply, Prod.mk.eta]
    rw [← Matrix.isUnit_iff_isUnit_det]; exact isUnit_F' r c i j

abbrev transition_Spec (i j : Basis (Fin (r + c)) K V) :=
  Spec.map (CommRingCat.ofHom (transition r c i j).toRingHom)

lemma transition_transition_Spec (i j : Basis (Fin (r + c)) K V) :
    transition_Spec r c i j ≫ transition_Spec r c j i = 𝟙 _ := by
  simp only [transition_Spec]
  rw [← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom ((transition r c i j).comp (transition r c j i)).toRingHom) = _
  rw [transition_transition]
  change Spec.map (𝟙 _) = _
  rw [Spec.map_id]

/-- The `RingHom` version of the action on functions of the gluing morphism from `V j k`
(morally, the intersection of the charts `U j` and `U k`, seen as a subscheme of `U j`) and the
fiber product of `V i j` and `V i k` over `U i`.-/
def transition'₁RingHom (i j k : Basis (Fin (r + c)) K V) :
    Localization.Away (equation r c j k) →+* (TensorProduct (MvPolynomial
    (Fin c × Fin r) K) (Localization.Away (equation r c i j))
    (Localization.Away (equation r c i k))) := by
  refine IsLocalization.Away.lift (equation r c j k) ?_
    (g := Algebra.TensorProduct.includeLeftRingHom.comp (transition_aux r c i j))
  rw [RingHom.comp_apply]; erw [transition_aux_equation, RingHom.map_mul, IsUnit.mul_iff]
  constructor
  · rw [← RingHom.comp_apply, Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap,
      RingHom.comp_apply]
    exact IsUnit.map Algebra.TensorProduct.includeRight (Localization.Away.map_unit _ _)
  · exact IsUnit.map Algebra.TensorProduct.includeLeftRingHom
      (IsLocalization.Away.invSelf_unit _ _)

/-- The `AlgHom` version of the action on functions of the gluing morphism from `V j k`
(morally, the intersection of the charts `U j` and `U k`, seen as a subscheme of `U j`) and the
fiber product of `V i j` and `V i k` over `U i`.-/
def transition'₁ (i j k : Basis (Fin (r + c)) K V) :
    Localization.Away (equation r c j k) →ₐ[K] (TensorProduct (MvPolynomial
    (Fin c × Fin r) K) (Localization.Away (equation r c i j))
    (Localization.Away (equation r c i k))) := by
  exact
  {
    transition'₁RingHom r c i j k with
    commutes' := by
      intro x
      simp only [transition'₁RingHom, AlgHom.coe_ringHom_mk, RingHom.mapMatrix_apply,
        MvPolynomial.comp_eval₂Hom, Algebra.TensorProduct.includeLeftRingHom_apply,
        RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, MonoidHom.coe_coe,
        Algebra.TensorProduct.algebraMap_apply]
      rw [IsScalarTower.algebraMap_apply (R := K) (S := functions_chart K r c)]
      rw [IsLocalization.Away.AwayMap.lift_eq]
      simp only [MvPolynomial.algebraMap_eq, MvPolynomial.eval₂Hom_C, RingHom.coe_comp,
        Function.comp_apply, Algebra.TensorProduct.includeLeftRingHom_apply]
  }

/-- The gluing morphism from `V j k` (morally, the intersection of the charts `U j` and `U k`,
seen as a subscheme of `U j`) and the fiber product of `V i j` and `V i k` over `U i`.-/
def transition'₁_Spec (i j k : Basis (Fin (r + c)) K V) :
    Limits.pullback (open_immersion r c i j) (open_immersion r c i k) ⟶
    Spec (CommRingCat.of (Localization.Away (equation r c j k))) :=
  (pullbackSpecIso (MvPolynomial (Fin c × Fin r) K)
    (Localization.Away (equation r c i j)) (Localization.Away (equation r c i k))).hom ≫
    Spec.map (CommRingCat.ofHom (transition'₁ r c i j k))

abbrev matrix_F''ij (i j k : Basis (Fin (r + c)) K V) :=
  (algebraMap (MvPolynomial (Fin c × Fin r) K)
  (TensorProduct (MvPolynomial (Fin c × Fin r) K) (Localization.Away
  (equation r c i j)) (Localization.Away (equation r c i k)))).mapMatrix (matrix_F r c i j)

abbrev matrix_G''ij (i j k : Basis (Fin (r + c)) K V) :=
  (matrix_G r c i j).map
  (algebraMap (MvPolynomial (Fin c × Fin r) K)
  (TensorProduct (MvPolynomial (Fin c × Fin r) K) (Localization.Away
  (equation r c i j)) (Localization.Away (equation r c i k))))

abbrev matrix_F''ik (i j k : Basis (Fin (r + c)) K V) :=
  (algebraMap (MvPolynomial (Fin c × Fin r) K)
  (TensorProduct (MvPolynomial (Fin c × Fin r) K) (Localization.Away
  (equation r c i j)) (Localization.Away (equation r c i k)))).mapMatrix (matrix_F r c i k)

lemma matrix_F''ij_inv_eq (i j k : Basis (Fin (r + c)) K V) :
    (matrix_F''ij r c i j k)⁻¹ =
    RingHom.mapMatrix Algebra.TensorProduct.includeLeftRingHom (matrix_F' r c i j)⁻¹ := by
  conv_rhs => rw [Matrix.nonsing_inv_eq_ring_inverse]
              change AlgHom.mapMatrix (R := functions_chart K r c)
                Algebra.TensorProduct.includeLeft (Ring.inverse (matrix_F' r c i j))
              rw [AlgHom.map_inv (f := Algebra.TensorProduct.includeLeft.mapMatrix)
              (α := Matrix (Fin r) (Fin r) (Localization.Away (equation r c i j)))
              (β := Matrix (Fin r) (Fin r) (TensorProduct (MvPolynomial
              (Fin c × Fin r) K) (Localization.Away (equation r c i j))
              (Localization.Away (equation r c i k)))) _ (isUnit_F' r c i j)]
  rw [Matrix.nonsing_inv_eq_ring_inverse, matrix_F']
  conv_rhs => rw [AlgHom.mapMatrix_apply, RingHom.mapMatrix_apply, Matrix.map_map]
              erw [← RingHom.coe_comp, ← Algebra.TensorProduct.algebraMap]
              rw [← RingHom.mapMatrix_apply]

lemma matrix_F''ik_inv_eq (i j k : Basis (Fin (r + c)) K V) :
    (matrix_F''ik r c i j k)⁻¹ =
    AlgHom.mapMatrix Algebra.TensorProduct.includeRight (matrix_F' r c i k)⁻¹ := by
  conv_rhs => rw [Matrix.nonsing_inv_eq_ring_inverse]
              rw [AlgHom.map_inv (f := Algebra.TensorProduct.includeRight.mapMatrix)
              (α := Matrix (Fin r) (Fin r) (Localization.Away (equation r c i k)))
              (R := MvPolynomial (Fin c × Fin r) K)
              (β := Matrix (Fin r) (Fin r) (TensorProduct (MvPolynomial
              (Fin c × Fin r) K) (Localization.Away (equation r c i j))
              (Localization.Away (equation r c i k)))) _ (isUnit_F' r c i k)]
  rw [Matrix.nonsing_inv_eq_ring_inverse, matrix_F']
  have heq : Algebra.TensorProduct.includeRight ∘ (algebraMap (MvPolynomial
    (Fin c × Fin r) K) (Localization.Away (equation r c i k))) =
    algebraMap _ (TensorProduct (MvPolynomial
    (Fin c × Fin r) K) (Localization.Away (equation r c i j))
    (Localization.Away (equation r c i k))) := by
    ext _
    simp only [Function.comp_apply, AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply]
  rw [AlgHom.mapMatrix_apply, RingHom.mapMatrix_apply, Matrix.map_map, heq]
  rw [matrix_F''ik, RingHom.mapMatrix_apply]

abbrev matrix_G''ik (i j k : Basis (Fin (r + c)) K V) :=
  (matrix_G r c i k).map
  (algebraMap (MvPolynomial (Fin c × Fin r) K)
  (TensorProduct (MvPolynomial (Fin c × Fin r) K) (Localization.Away
  (equation r c i j)) (Localization.Away (equation r c i k))))

lemma matrix_F''ij_isUnit (i j k : Basis (Fin (r + c)) K V) :
    IsUnit (matrix_F''ij r c i j k) := by
  rw [matrix_F''ij, Algebra.TensorProduct.algebraMap, ← RingHom.mapMatrix_comp, RingHom.comp_apply]
  apply IsUnit.map
  exact isUnit_F' r c i j

lemma transition'₁_algebraMap (i j k : Basis (Fin (r + c)) K V) :
    (transition'₁RingHom r c i j k).comp (algebraMap (functions_chart K r c) _) =
    Algebra.TensorProduct.includeLeftRingHom.comp (transition_aux r c i j) := by
  rw [transition'₁RingHom, IsLocalization.Away.AwayMap.lift_comp]

lemma transition'₁_F' (i j k : Basis (Fin (r + c)) K V) :
    (matrix_F' r c j k).map (transition'₁ r c i j k) =
    (matrix_F''ik r c i j k) * (matrix_F''ij r c i j k)⁻¹ := by
  rw [matrix_F', transition'₁]; erw [← RingHom.mapMatrix_apply]
  conv_lhs => change (transition'₁RingHom r c i j k).mapMatrix
                ((algebraMap (functions_chart K r c) _).mapMatrix (matrix_F r c j k))
              rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, Matrix.map_map]
              rw [← RingHom.coe_comp]
              rw [transition'₁_algebraMap, RingHom.coe_comp, ← Matrix.map_map]
              erw [transition_aux_F]
              rw [RingHom.map_matrix_mul']
              congr; rw [Matrix.map_map]; erw [← RingHom.coe_comp]
              rw [← Algebra.TensorProduct.algebraMap]; rfl
              erw [← RingHom.mapMatrix_apply]; rw [← matrix_F''ij_inv_eq]
  rfl

lemma transition'₁_F'_inv (i j k : Basis (Fin (r + c)) K V) :
    (matrix_F' r c j k)⁻¹.map (transition'₁ r c i j k) =
    (matrix_F''ij r c i j k) * (matrix_F''ik r c i j k)⁻¹ := by
  rw [← AlgHom.mapMatrix_apply, Matrix.nonsing_inv_eq_ring_inverse]
  rw [AlgHom.map_inv (f := (transition'₁ r c i j k).mapMatrix)
    (α := Matrix (Fin r) (Fin r) (Localization.Away (equation r c j k)))
    (β := Matrix (Fin r) (Fin r) (TensorProduct (MvPolynomial (Fin c × Fin r) K)
    (Localization.Away (equation r c i j)) (Localization.Away (equation r c i k))))
    (hx := isUnit_F' r c j k)]
  rw [AlgHom.mapMatrix_apply, transition'₁_F', ← Matrix.nonsing_inv_eq_ring_inverse
  ((matrix_F''ik r c i j k * (matrix_F''ij r c i j k)⁻¹))]
  rw [Matrix.mul_inv_rev (matrix_F''ik r c i j k)]
  rw [Matrix.nonsing_inv_nonsing_inv]
  rw [← Matrix.isUnit_iff_isUnit_det]
  exact matrix_F''ij_isUnit r c i j k

lemma transition'₁_G' (i j k : Basis (Fin (r + c)) K V) :
    (matrix_G' r c j k).map (transition'₁ r c i j k) =
    (matrix_G''ik r c i j k) * (matrix_F''ij r c i j k)⁻¹ := by
  rw [matrix_G', transition'₁, Matrix.map_map]; erw [← RingHom.coe_comp]
  conv_lhs => change (matrix_G r c j k).map ((transition'₁RingHom r c i j k).comp (algebraMap
                (functions_chart K r c) _))
              rw [transition'₁_algebraMap, RingHom.coe_comp, ← Matrix.map_map]
              erw [transition_aux_G]
              rw [RingHom.map_matrix_mul']
              congr; rw [Matrix.map_map]; erw [← RingHom.coe_comp]
              rw [← Algebra.TensorProduct.algebraMap]; rfl
              erw [← RingHom.mapMatrix_apply]; rw [← matrix_F''ij_inv_eq]


lemma immersion_transition'₁_Spec (i j k : Basis (Fin (r + c)) K V) :
    transition'₁_Spec r c i j k ≫ open_immersion r c j k =
    (Limits.pullback.fst ≫ transition_Spec r c i j) ≫ open_immersion r c j i := by
  rw [transition'₁_Spec, transition'₁]
  conv_lhs => congr; congr; rfl; change Spec.map (CommRingCat.ofHom (transition'₁RingHom r c i j k))
  rw [transition'₁RingHom]
  rw [← cancel_epi (f := (pullbackSpecIso (MvPolynomial (Fin c × Fin r) K)
    (Localization.Away (equation r c i j)) (Localization.Away (equation r c i k))).inv)]
  rw [← Category.assoc, ← Category.assoc, Iso.inv_hom_id, Category.id_comp, ← Category.assoc]
  rw [← Category.assoc, pullbackSpecIso_inv_fst]
  conv_rhs => rw [Spec.algebraMap, open_immersion, ← Spec.map_comp, ← Spec.map_comp]
  conv_lhs => rw [open_immersion, ← Spec.map_comp]
  apply congrArg Spec.map
  rw [← CommRingCat.ringHom_comp_eq_comp, ← Category.assoc, ← CommRingCat.ringHom_comp_eq_comp]
  conv_rhs => change CommRingCat.ofHom ((transition r c i j).toRingHom.comp (algebraMap _ _)) ≫
    CommRingCat.ofHom (algebraMap _ _)
              rw [← CommRingCat.ringHom_comp_eq_comp]
  rw [transition]
  rw [IsLocalization.Away.AwayMap.lift_comp, IsLocalization.Away.AwayMap.lift_comp]
  rfl

lemma transition'₁_transition (i j k : Basis (Fin (r + c)) K V) :
    transition'₁_Spec r c i j k ≫ transition_Spec r c j k ≫ open_immersion r c k j =
    Limits.pullback.snd ≫ transition_Spec r c i k ≫ open_immersion r c k i := by
  rw [transition'₁_Spec]
  rw [← cancel_epi (f := (pullbackSpecIso (MvPolynomial (Fin c × Fin r) K)
    (Localization.Away (equation r c i j)) (Localization.Away (equation r c i k))).inv)]
  rw [← Category.assoc, ← Category.assoc, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  conv_rhs => rw [← Category.assoc, pullbackSpecIso_inv_snd, transition_Spec, open_immersion]
              rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ringHom_comp_eq_comp]
              change Spec.map (CommRingCat.ofHom ((transition r c i k).toRingHom.comp
                (algebraMap _ _)) ≫ CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom)
              rw [← CommRingCat.ringHom_comp_eq_comp]
  conv_lhs => rw [open_immersion, ← Spec.map_comp, ← Spec.map_comp, ← Category.assoc,
                ← CommRingCat.ringHom_comp_eq_comp]
              erw [← CommRingCat.ringHom_comp_eq_comp]
  apply congrArg Spec.map
  conv_lhs => congr; rfl; change (transition r c j k).toRingHom.comp (algebraMap _ _)
              rw [transition, IsLocalization.Away.AwayMap.lift_comp]
  rw [IsLocalization.Away.AwayMap.lift_comp]
  rw [← AlgHom.comp_toRingHom]
  conv_rhs => change (Algebra.TensorProduct.includeRight.restrictScalars (R := K)).toRingHom.comp
                (transition_aux r c i k).toRingHom
              erw [← AlgHom.comp_toRingHom (R := K)
                (φ₁ := Algebra.TensorProduct.includeRight.restrictScalars (R := K))
                (φ₂ := transition_aux r c i k)]
  rw [← AlgHom.toRingHom_eq_coe, ← AlgHom.toRingHom_eq_coe]
  apply congrArg (fun (s : functions_chart K r c →ₐ[K]
    TensorProduct (MvPolynomial (Fin c × Fin r) K)
    (Localization.Away (equation r c i j)) (Localization.Away (equation r c i k))) ↦ s.toRingHom)
  refine MvPolynomial.algHom_ext (fun pq ↦ ?_)
  suffices h : (matrix_X K r c).map ((transition'₁ r c i j k).comp (transition_aux r c j k)) =
      (matrix_X K r c).map ((Algebra.TensorProduct.includeRight.restrictScalars (R := K)).comp
      (transition_aux r c i k)) by
    have heq : matrix_X K r c pq.1 pq.2 = MvPolynomial.X pq := rfl
    conv_lhs => rw [← heq, ← Matrix.map_apply (f := (transition'₁ r c i j k).comp
                  (transition_aux r c j k)), h]
    simp only [AlgHom.coe_comp, AlgHom.coe_restrictScalars', AlgHom.coe_mk, RingHom.mapMatrix_apply,
      MvPolynomial.coe_eval₂Hom, map_apply, of_apply, Prod.mk.eta, Function.comp_apply,
      MvPolynomial.eval₂_X, Algebra.TensorProduct.includeRight_apply]
  rw [AlgHom.coe_comp, ← Matrix.map_map, transition_aux_matrix_X]; erw [RingHom.map_matrix_mul']
  erw [transition'₁_G', transition'₁_F'_inv]
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (matrix_F''ij r c i j k)⁻¹]
  rw [Matrix.nonsing_inv_mul _
    (by rw [← Matrix.isUnit_iff_isUnit_det]; exact matrix_F''ij_isUnit r c i j k), Matrix.one_mul]
  rw [AlgHom.coe_comp, ← Matrix.map_map, transition_aux_matrix_X]; erw [RingHom.map_matrix_mul']
  have heq : ((AlgHom.restrictScalars K Algebra.TensorProduct.includeRight).toRingHom).toFun ∘
    (algebraMap (MvPolynomial (Fin c × Fin r) K) (Localization.Away
    (equation r c i k))) = algebraMap _ (TensorProduct (MvPolynomial
    (Fin c × Fin r) K) (Localization.Away (equation r c i j))
    (Localization.Away (equation r c i k))) := by
    ext x
    simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_restrictScalars, RingHom.toMonoidHom_eq_coe,
      OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, MonoidHom.coe_coe, RingHom.coe_coe,
      Function.comp_apply, AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply]
  conv_rhs => congr; rw [matrix_G', Matrix.map_map, heq]; change matrix_G''ik r c i j k
  conv_rhs => congr; rfl; erw [← RingHom.mapMatrix_apply]
              change Algebra.TensorProduct.includeRight.toRingHom.mapMatrix (matrix_F' r c i k)⁻¹
              erw [← matrix_F''ik_inv_eq]

variable (K V)

/-- The gluing data defining the Grassmannian scheme. The type indexing the charts is
`Basis (Fin (r + c)) K V`.
If `i` is in `Basis (Fin (r + c)) K V`, then the corresponding chart `U i` is the spectrum of
the `K`-algebra of multivariable polynomials with indeterminates indexed by `Fin c × Fin r`, or
in other words `Spec (MvPolynomial (Fin c × Fin r) K)`.
If `i` and `j` are in `Basis (Fin (r + c)) K V`, then we define a scheme `V i j`, which is morally
the intersection of `U i` and `U j` (i.e. their fiber product over the Grassmannian), seen as
a subscheme of `U i`. We take `V i j` to be the basic open subset of `U i` defined by the
function `equation r c i j`, with the canonical morphism `f i j` to `U i`, which is an open
immersion.
If `i` and `j` are in `Basis (Fin (r + c)) K V`, we have an isomorphism `t i j` from
`V i j` to `V j i`, which we define in the following way: An element of `V i j` is a `c × r`
matrix `A`. Consider the map `φ : V →ₗ[K] (Fin r → K)` whose matrix `M₁` in the basis `i` of
`V` and the canonical basis of `Fin r → K` is obtained by stacking the `r × r` identity matrix
on top of `A`. We multiply `M₁` on the left by the change of basis matrix `B j i` from `j` to
`i`, in order to get the matrix `M₂` of `φ` in the basis `j` of `V` and the canonical basis
of `Fin r → K`. Because we are in the open subscheme `V i j`, the top `r × r` submatrix `F`
of `M₂` is invertible, and we divide `M₂` by `F`, then taken the bottom `c × r` matrix to get
an element of `U j`, which happens to be in `V j i`.
If `i`, `j` and `k` are in `Basis (Fin (r + c)) K V`, we need to define a gluing morphism
`t' i j k` from `V i j × V i k` (fiber product over `U i`) to `V j k × V j i` (fiber product over
`U j`). The condition `t_fac i j k` says that this morphism should be obtained by "restriction"
(via the first projection on `V i j × V i k` and the second projection on `V j k × V j i`) of
`t' i j : V i j ⟶ V j i`, so we just need to prove that `t' i j` does restrict to a morphism
betweem the fiber products.
Finally, the cocycle condition on the gluing morphisms `t' i j k` is expressed by the
field `cocycle i j k`.
-/
def glueData : GlueData where
  J := Basis (Fin (r + c)) K V
  U _ := chart K r c
  V ij := Spec (CommRingCat.of (Localization.Away (equation r c ij.1 ij.2)))
  f i j := open_immersion r c i j
  f_mono _ _ := inferInstance
  f_hasPullback := inferInstance
  f_id i := by
    simp only [open_immersion]
    suffices h : IsIso ((CommRingCat.ofHom (algebraMap (MvPolynomial
      (Fin c × Fin r) K) (Localization.Away (equation r c i i))))) by
      exact inferInstance
    rw [equation_eq_one_of_diagonal]
    exact localization_unit_isIso (CommRingCat.of
      (MvPolynomial ((Fin c) × Fin r) K))
  t i j := transition_Spec r c i j
  t_id i := by
    simp only [transition_Spec, transition, AlgHom.coe_ringHom_mk, RingHom.mapMatrix_apply, id_eq]
    rw [← Spec.map_id]
    apply congrArg
    change _ = CommRingCat.ofHom (RingHom.id _)
    apply congrArg
    apply IsLocalization.ringHom_ext (R := MvPolynomial (Fin c × Fin r) K)
      (M := Submonoid.powers (equation r c i i))
    ext x
    · simp only [AlgHom.coe_ringHom_mk, RingHom.mapMatrix_apply,
      IsLocalization.Away.AwayMap.lift_comp, RingHom.coe_comp, MvPolynomial.coe_eval₂Hom,
      Function.comp_apply, MvPolynomial.eval₂_C, RingHomCompTriple.comp_eq]
      rw [← MvPolynomial.algebraMap_eq]
      rw [IsScalarTower.algebraMap_apply K (MvPolynomial (Fin c × Fin r) K)]
    · simp only [AlgHom.coe_ringHom_mk, RingHom.mapMatrix_apply,
      IsLocalization.Away.AwayMap.lift_comp, MvPolynomial.eval₂Hom_X', RingHomCompTriple.comp_eq]
      simp_rw [matrix_F_eq_id_of_diagonal]
      simp_rw [matrix_G'_eq_X_of_diagonal]
      simp only [map_zero, _root_.map_one, Matrix.map_one, inv_one, Matrix.mul_one, of_apply,
        Prod.mk.eta]
  t' i j k := by
    refine Limits.pullback.lift (transition'₁_Spec r c i j k)
      (Limits.pullback.fst ≫ transition_Spec r c i j) ?_
    exact immersion_transition'₁_Spec _ _ _ _ _
  t_fac i j k := by rw [Limits.pullback.lift_snd]
  cocycle i j k := by
    simp only
    rw [← cancel_mono Limits.pullback.snd]
    conv_lhs => rw [Category.assoc, Category.assoc]
                congr; rfl; congr; rfl
                rw [Limits.pullback.lift_snd]
    slice_lhs 2 3 => rw [Limits.pullback.lift_fst]
    rw [← cancel_mono (f := open_immersion r c i k), Category.assoc, Category.assoc]
    rw [transition'₁_transition, Category.id_comp, ← Category.assoc, Limits.pullback.lift_snd]
    slice_lhs 2 3 => rw [transition_transition_Spec]
    rw [Category.id_comp, Limits.pullback.condition]
  f_open _ _ := inferInstance

end Grassmannian

def Grassmannian := (Grassmannian.glueData K V r c).glued
-- Note that this is empty unless `finrank K v = r + c`.

namespace Grassmannian

def structMorphism : Grassmannian K V r c ⟶ Spec (CommRingCat.of K) := by
  refine Scheme.GlueData.glueMorphisms (Grassmannian.glueData K V r c)
    (fun _ ↦ Spec.map (CommRingCat.ofHom (algebraMap _ _))) ?_
  intro i j
  simp only [glueData, open_immersion, transition_Spec]
  rw [← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  conv_lhs =>  change (algebraMap _ (Localization.Away (equation r c i j))).comp
                 (algebraMap K (functions_chart K r c))
               rw [← IsScalarTower.algebraMap_eq K]
  conv_rhs => congr; change (algebraMap _ (Localization.Away (equation r c j i))).comp
                 (algebraMap K (functions_chart K r c))
              rw [← IsScalarTower.algebraMap_eq K]
  conv_rhs => change (transitionRingHom r c i j).comp (algebraMap K _)
  simp only [CommRingCat.coe_of, transitionRingHom, AlgHom.coe_ringHom_mk, RingHom.mapMatrix_apply]
  conv_rhs => rw [IsScalarTower.algebraMap_eq K (functions_chart K r c), ← RingHom.comp_assoc,
                IsLocalization.Away.AwayMap.lift_comp, AlgHom.comp_algebraMap]

end Grassmannian
