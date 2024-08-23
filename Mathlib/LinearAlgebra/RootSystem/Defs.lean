/-
Copyright (c) 2023 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash, Deepro Choudhury, Scott Carnahan
-/
import Mathlib.LinearAlgebra.PerfectPairing
import Mathlib.LinearAlgebra.Reflection

/-!
# Root data and root systems

This file contains basic definitions for root systems and root data.  We introduce a generalization
of both concepts, called a root pairing.  A typical example of a root pairing is given by choosing a
quadratic form and taking a union of spheres of various radii.  When integrality conditions are
imposed, the property that the set of roots is closed under reflection forces the radii to be small.

## Main definitions:

 * `RootPairing`: Given two perfectly-paired `R`-modules `M` and `N` (over some commutative ring
   `R`) a root pairing with indexing set `ι` is the data of an `ι`-indexed subset of `M`
   ("the roots") an `ι`-indexed subset of `N` ("the coroots"), and an `ι`-indexed set of
   permutations of `ι` such that each root-coroot pair evaluates to `2`, and the permutation
   attached to each element of `ι` is compatible with the reflections on the corresponding roots and
   coroots.
 * `RootDatum`: A root datum is a root pairing for which the roots and coroots take values in
   finitely-generated free Abelian groups.
 * `RootSystem`: A root system is a root pairing for which the roots span their ambient module.
 * `RootPairing.IsCrystallographic`: A root pairing is said to be crystallographic if the pairing
   between a root and coroot is always an integer.
 * `RootPairing.IsReduced`: A root pairing is said to be reduced if two linearly dependent roots are
   always related by a sign.
 * `RootPairing.weylGroup`: The group of linear isomorphisms on `M` generated by reflections.
 * `RootPairing.weylGroupToPerm`: The permutation representation of the Weyl group on `ι`.

## TODO

 * When is the permutation representation faithful? basic counterexample: char 2 rank 2 one root.
 * Base change of root pairings (may need flatness; perhaps should go in a different file).
 * Isomorphism of root pairings.
 * Crystallographic root systems are isomorphic to base changes of root systems over `ℤ`: Take
   `M₀` and `N₀` to be the `ℤ`-span of roots and coroots.

## Implementation details

A root datum is sometimes defined as two subsets: roots and coroots, together with a bijection
between them, subject to hypotheses. However the hypotheses ensure that the bijection is unique and
so the question arises of whether this bijection should be part of the data of a root datum or
whether one should merely assert its existence. For finite root systems, things are even more
extreme: the coroots are uniquely determined by the roots, and furthermore, there is a canonical
non-degenerate bilinear form on the ambient space.  Many informal accounts even include this form
as part of the data.

We have opted for a design in which the uniquely-determined data is included: the bijection
between roots and coroots is (implicitly) included and the coroots are included for root systems.
Empirically this seems to be by far the most convenient design and by providing extensionality
lemmas expressing the uniqueness we expect to get the best of both worlds.

Furthermore, we require roots and coroots to be injections from a base indexing type `ι` rather than
subsets of their codomains. This design was chosen to avoid the bijection between roots and coroots
being a dependently-typed object. A third option would be to have the roots and coroots be subsets
but to avoid having a dependently-typed bijection by defining it globally with junk value `0`
outside of the roots and coroots. This would work but lacks the convenient symmetry that the chosen
design enjoys: by introducing the indexing type `ι`, one does not have to pick a direction
(`roots → coroots` or `coroots → roots`) for the forward direction of the bijection. Besides,
providing the user with the additional definitional power to specify an indexing type `ι` is a
benefit and the junk-value pattern is a cost.

As a final point of divergence from the classical literature, we make the reflection permutation on
roots and coroots explicit, rather than specifying only that reflection preserves the sets of roots
and coroots. This is necessary when working with infinite root systems, where the coroots are not
uniquely determined by the roots, because without it, the reflection permutations on roots and
coroots may not correspond. For this purpose, we define a map from `ι` to permutations on `ι`, and
require that it is compatible with reflections and coreflections.

-/

open Set Function
open Module hiding reflection
open Submodule (span)
open AddSubgroup (zmultiples)

noncomputable section

variable (ι R M N : Type*)
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- Given two perfectly-paired `R`-modules `M` and `N`, a root pairing with indexing set `ι`
is the data of an `ι`-indexed subset of `M` ("the roots"), an `ι`-indexed subset of `N`
("the coroots"), and an `ι`-indexed set of permutations of `ι`, such that each root-coroot pair
evaluates to `2`, and the permutation attached to each element of `ι` is compatible with the
reflections on the corresponding roots and coroots.

It exists to allow for a convenient unification of the theories of root systems and root data. -/
structure RootPairing extends PerfectPairing R M N :=
  /-- A parametrized family of vectors, called roots. -/
  root : ι ↪ M
  /-- A parametrized family of dual vectors, called coroots. -/
  coroot : ι ↪ N
  root_coroot_two : ∀ i, toLin (root i) (coroot i) = 2
  /-- A parametrized family of permutations, induced by reflection. -/
  reflection_perm : ι → (ι ≃ ι)
  reflection_perm_root : ∀ i j,
    root j - toLin (root j) (coroot i) • root i = root (reflection_perm i j)
  reflection_perm_coroot : ∀ i j,
    coroot j - toLin (root i) (coroot j) • coroot i = coroot (reflection_perm i j)

/-- A root datum is a root pairing with coefficients in the integers and for which the root and
coroot spaces are finitely-generated free Abelian groups.

Note that the latter assumptions `[Free ℤ X₁] [Finite ℤ X₁] [Free ℤ X₂] [Finite ℤ X₂]` should be
supplied as mixins. -/
abbrev RootDatum (X₁ X₂ : Type*) [AddCommGroup X₁] [AddCommGroup X₂] := RootPairing ι ℤ X₁ X₂

/-- A root system is a root pairing for which the roots span their ambient module.

Note that this is slightly more general than the usual definition in the sense that `N` is not
required to be spanned by coroots`. -/
structure RootSystem extends RootPairing ι R M N :=
  span_eq_top : span R (range root) = ⊤

attribute [simp] RootSystem.span_eq_top

namespace RootPairing

variable {ι R M N}
variable (P : RootPairing ι R M N) (i j : ι)

lemma ne_zero [CharZero R] : (P.root i : M) ≠ 0 :=
  fun h ↦ by simpa [h] using P.root_coroot_two i

lemma ne_zero' [CharZero R] : (P.coroot i : N) ≠ 0 :=
  fun h ↦ by simpa [h] using P.root_coroot_two i

/-- If we interchange the roles of `M` and `N`, we still have a root pairing. -/
protected def flip : RootPairing ι R N M :=
  { P.toPerfectPairing.flip with
    root := P.coroot
    coroot := P.root
    root_coroot_two := P.root_coroot_two
    reflection_perm := P.reflection_perm
    reflection_perm_root := P.reflection_perm_coroot
    reflection_perm_coroot := P.reflection_perm_root }

@[simp]
lemma flip_flip : P.flip.flip = P :=
  rfl

/-- This is the pairing between roots and coroots. -/
def pairing : R := P.toLin (P.root i) (P.coroot j)

@[simp]
lemma root_coroot_eq_pairing : P.toLin (P.root i) (P.coroot j) = P.pairing i j :=
  rfl

lemma coroot_root_eq_pairing : P.toLin.flip (P.coroot i) (P.root j) = P.pairing j i := by
  simp

@[simp]
lemma pairing_same : P.pairing i i = 2 := P.root_coroot_two i

lemma coroot_root_two :
    P.toLin.flip (P.coroot i) (P.root i) = 2 := by
  simp

/-- The reflection associated to a root. -/
def reflection : M ≃ₗ[R] M :=
  Module.reflection (P.flip.root_coroot_two i)

@[simp]
lemma root_reflection_perm (j : ι) :
    P.root ((P.reflection_perm i) j) = (P.reflection i) (P.root j) :=
  (P.reflection_perm_root i j).symm

theorem mapsTo_reflection_root : MapsTo (P.reflection i) (range P.root) (range P.root) := by
  rintro - ⟨j, rfl⟩
  exact P.root_reflection_perm i j ▸ mem_range_self (P.reflection_perm i j)

lemma reflection_apply (x : M) :
    P.reflection i x = x - (P.toLin x (P.coroot i)) • P.root i :=
  rfl

lemma reflection_apply_root :
    P.reflection i (P.root j) = P.root j - (P.pairing j i) • P.root i :=
  rfl

@[simp]
lemma reflection_apply_self :
    P.reflection i (P.root i) = - P.root i :=
  Module.reflection_apply_self (P.coroot_root_two i)

@[simp]
lemma reflection_same (x : M) :
    P.reflection i (P.reflection i x) = x :=
  Module.involutive_reflection (P.coroot_root_two i) x

@[simp]
lemma reflection_inv :
    (P.reflection i)⁻¹ = P.reflection i :=
  rfl

@[simp]
lemma reflection_sq :
    P.reflection i ^ 2 = 1 :=
  mul_eq_one_iff_eq_inv.mpr rfl

@[simp]
lemma reflection_perm_sq :
    P.reflection_perm i ^ 2 = 1 := by
  ext j
  refine Embedding.injective P.root ?_
  simp only [sq, Equiv.Perm.mul_apply, root_reflection_perm, reflection_same, Equiv.Perm.one_apply]

@[simp]
lemma reflection_perm_inv :
    (P.reflection_perm i)⁻¹ = P.reflection_perm i :=
  (mul_eq_one_iff_eq_inv.mp <| P.reflection_perm_sq i).symm

lemma bijOn_reflection_root :
    BijOn (P.reflection i) (range P.root) (range P.root) :=
  Module.bijOn_reflection_of_mapsTo _ <| P.mapsTo_reflection_root i

@[simp]
lemma reflection_image_eq :
    P.reflection i '' (range P.root) = range P.root :=
  (P.bijOn_reflection_root i).image_eq

/-!
theorem involutive_reflection : Involutive (P.reflection i) :=
  Module.involutive_reflection (P.flip.root_coroot_two i)
-/

/-- The reflection associated to a coroot. -/
def coreflection : N ≃ₗ[R] N :=
  Module.reflection (P.root_coroot_two i)

@[simp]
lemma coroot_reflection_perm (j : ι) :
    P.coroot (P.reflection_perm i j) = (P.coreflection i) (P.coroot j) :=
  (P.reflection_perm_coroot i j).symm

theorem mapsTo_coreflection_coroot :
    MapsTo (P.coreflection i) (range P.coroot) (range P.coroot) := by
  rintro - ⟨j, rfl⟩
  exact P.coroot_reflection_perm i j ▸ mem_range_self (P.reflection_perm i j)

lemma coreflection_apply (f : N) :
    P.coreflection i f = f - (P.toLin (P.root i) f) • P.coroot i :=
  rfl

lemma coreflection_apply_coroot :
    P.coreflection i (P.coroot j) = P.coroot j - (P.pairing i j) • P.coroot i :=
  rfl

@[simp]
lemma coreflection_apply_self :
    P.coreflection i (P.coroot i) = - P.coroot i :=
  Module.reflection_apply_self (P.flip.coroot_root_two i)

@[simp]
lemma coreflection_same (x : N) :
    P.coreflection i (P.coreflection i x) = x :=
  Module.involutive_reflection (P.flip.coroot_root_two i) x

@[simp]
lemma coreflection_inv :
    (P.coreflection i)⁻¹ = P.coreflection i :=
  rfl

@[simp]
lemma coreflection_sq :
    P.coreflection i ^ 2 = 1 :=
  mul_eq_one_iff_eq_inv.mpr rfl

lemma bijOn_coreflection_coroot : BijOn (P.coreflection i) (range P.coroot) (range P.coroot) :=
  bijOn_reflection_root P.flip i

@[simp]
lemma coreflection_image_eq :
    P.coreflection i '' (range P.coroot) = range P.coroot :=
  (P.bijOn_coreflection_coroot i).image_eq

lemma coreflection_eq_flip_reflection :
    P.coreflection i = P.flip.reflection i :=
  rfl

lemma reflection_dualMap_eq_coreflection :
    (P.reflection i).dualMap ∘ₗ P.toLin.flip = P.toLin.flip ∘ₗ P.coreflection i := by
  ext n m
  simp [coreflection_apply, reflection_apply, mul_comm (P.toLin m (P.coroot i))]

lemma coroot_eq_coreflection_of_root_eq
    {i j k : ι} (hk : P.root k = P.reflection i (P.root j)) :
    P.coroot k = P.coreflection i (P.coroot j) := by
  rw [← P.root_reflection_perm, EmbeddingLike.apply_eq_iff_eq] at hk
  rw [← P.coroot_reflection_perm, hk]

@[simp]
lemma reflection_perm_self : P.reflection_perm i (P.reflection_perm i j) = j := by
  refine (Embedding.injective P.root) ?_
  simp only [root_reflection_perm, reflection_same]

lemma reflection_perm_square : (P.reflection_perm i) ^[2] = id := by
  ext j
  simp only [iterate_succ, iterate_zero, CompTriple.comp_eq, comp_apply, reflection_perm_self,
    id_eq]

lemma reflection_eq (x y : M) (h : P.reflection i x = P.reflection i y) : x = y := by
  simp only [reflection, Module.reflection, Equiv.invFun_as_coe, Involutive.toPerm_symm,
    Involutive.coe_toPerm, EmbeddingLike.apply_eq_iff_eq] at h
  exact h

lemma scalar_mul_eq_two (x : M) (c : R) (i : ι) (h : P.root i = c • x) :
    c * P.toLin x (P.coroot i) = 2 := by
  rw [← smul_eq_mul, (LinearMap.map_smul₂ P.toLin c x (P.coroot i)).symm, ← h, P.root_coroot_two i]

lemma reflection_eq_imp_scalar (j : ι) (h: P.reflection i = P.reflection j) :
    2 • P.root i = (P.toLin (P.root i) (P.coroot j)) • P.root j := by
  have hij: P.root i = -P.root i + P.toLin (P.root i) (P.coroot j) • P.root j := by
    nth_rw 1 [← reflection_same P i (P.root i), reflection_apply_self, h, reflection_apply]
    rw [LinearMap.map_neg₂, neg_smul, sub_neg_eq_add]
  rw [two_nsmul, eq_neg_add_iff_add_eq.mp hij]

lemma coreflection_eq_imp_scalar (j : ι) (h: P.coreflection i = P.coreflection j) :
    2 • P.coroot i = (P.toLin (P.root j) (P.coroot i)) • P.coroot j := by
  have hij: P.coroot i = -P.coroot i + P.toLin (P.root j) (P.coroot i) • P.coroot j := by
    nth_rw 1 [← coreflection_same P i (P.coroot i), coreflection_apply_self, h, coreflection_apply]
    rw [LinearMap.map_neg, neg_smul, sub_neg_eq_add]
  rw [two_nsmul, eq_neg_add_iff_add_eq.mp hij]

lemma reflection_mul (x : M) :
    (P.reflection i * P.reflection j) x = P.reflection i (P.reflection j x) := rfl

lemma root_coreflection (P : RootPairing ι R M N) (y : N) (i : ι) :
    (P.toLin (P.root i) (P.coreflection i y)) = - P.toLin (P.root i) y := by
  rw [coreflection_apply, map_sub, map_smul, root_coroot_two, smul_eq_mul, mul_comm, two_mul]
  abel

/-- A root pairing is said to be crystallographic if the pairing between a root and coroot is
always an integer. -/
def IsCrystallographic : Prop :=
  ∀ i, MapsTo (P.toLin (P.root i)) (range P.coroot) (zmultiples (1 : R))

lemma isCrystallographic_iff :
    P.IsCrystallographic ↔ ∀ i j, ∃ z : ℤ, z = P.pairing i j := by
  rw [IsCrystallographic]
  refine ⟨fun h i j ↦ ?_, fun h i _ ⟨j, hj⟩ ↦ ?_⟩
  · simpa [AddSubgroup.mem_zmultiples_iff] using h i (mem_range_self j)
  · simpa [← hj, AddSubgroup.mem_zmultiples_iff] using h i j

/-- A root pairing is said to be reduced if any linearly dependent pair of roots is related by a
sign. -/
def IsReduced : Prop :=
  ∀ i j, ¬ LinearIndependent R ![P.root i, P.root j] → (P.root i = P.root j ∨ P.root i = - P.root j)

lemma isReduced_iff : P.IsReduced ↔ ∀ i j : ι, i ≠ j →
    ¬ LinearIndependent R ![P.root i, P.root j] → P.root i = - P.root j := by
  rw [IsReduced]
  refine ⟨fun h i j hij hLin ↦ ?_, fun h i j hLin  ↦ ?_⟩
  · specialize h i j hLin
    simp_all only [ne_eq, EmbeddingLike.apply_eq_iff_eq, false_or]
  · by_cases h' : i = j
    · exact Or.inl (congrArg P.root h')
    · exact Or.inr (h i j h' hLin)

/-- The `Weyl group` of a root pairing is the group of automorphisms of the weight space generated
by reflections in roots. -/
def weylGroup : Subgroup (M ≃ₗ[R] M) :=
  Subgroup.closure (range P.reflection)

lemma reflection_mem_weylGroup : P.reflection i ∈ P.weylGroup :=
  Subgroup.subset_closure <| mem_range_self i

lemma mem_range_root_of_mem_range_reflection_of_mem_range_root
    {r : M ≃ₗ[R] M} {α : M} (hr : r ∈ range P.reflection) (hα : α ∈ range P.root) :
    r • α ∈ range P.root := by
  obtain ⟨i, rfl⟩ := hr
  obtain ⟨j, rfl⟩ := hα
  exact ⟨P.reflection_perm i j, P.root_reflection_perm i j⟩

lemma mem_range_coroot_of_mem_range_coreflection_of_mem_range_coroot
    {r : N ≃ₗ[R] N} {α : N} (hr : r ∈ range P.coreflection) (hα : α ∈ range P.coroot) :
    r • α ∈ range P.coroot := by
  obtain ⟨i, rfl⟩ := hr
  obtain ⟨j, rfl⟩ := hα
  exact ⟨P.reflection_perm i j, P.coroot_reflection_perm i j⟩

lemma exists_root_eq_smul_of_mem_weylGroup {w : M ≃ₗ[R] M} (hw : w ∈ P.weylGroup) (i : ι) :
    ∃ j, P.root j = w • P.root i :=
  Subgroup.smul_mem_of_mem_closure_of_mem (by simp)
    (fun _ h _ ↦ P.mem_range_root_of_mem_range_reflection_of_mem_range_root h) hw (mem_range_self i)

/-- The permutation representation of the Weyl group induced by `reflection_perm`. -/
def weylGroupToPerm : P.weylGroup →* Equiv.Perm ι where
  toFun w :=
  { toFun := fun i => (P.exists_root_eq_smul_of_mem_weylGroup (w := w.1) w.2 i).choose
    invFun := fun i => (P.exists_root_eq_smul_of_mem_weylGroup (w := w⁻¹.1) w⁻¹.2 i).choose
    left_inv := fun i => by
      obtain ⟨w, hw⟩ := w
      apply P.root.injective
      rw [(P.exists_root_eq_smul_of_mem_weylGroup ((Subgroup.inv_mem_iff P.weylGroup).mpr hw)
          ((P.exists_root_eq_smul_of_mem_weylGroup hw i).choose)).choose_spec,
        (P.exists_root_eq_smul_of_mem_weylGroup hw i).choose_spec, inv_smul_eq_iff]
    right_inv := fun i => by
      obtain ⟨w, hw⟩ := w
      have hw' : w⁻¹ ∈ P.weylGroup := (Subgroup.inv_mem_iff P.weylGroup).mpr hw
      refine Embedding.injective P.root ?_
      rw [(P.exists_root_eq_smul_of_mem_weylGroup hw
          ((P.exists_root_eq_smul_of_mem_weylGroup hw' i).choose)).choose_spec,
        (P.exists_root_eq_smul_of_mem_weylGroup hw' i).choose_spec, smul_inv_smul] }
  map_one' := by ext; simp
  map_mul' x y := by
    obtain ⟨x, hx⟩ := x
    obtain ⟨y, hy⟩ := y
    ext i
    apply P.root.injective
    simp only [Equiv.coe_fn_mk, Equiv.Perm.coe_mul, comp_apply]
    rw [(P.exists_root_eq_smul_of_mem_weylGroup (mul_mem hx hy) i).choose_spec,
      (P.exists_root_eq_smul_of_mem_weylGroup hx
        ((P.exists_root_eq_smul_of_mem_weylGroup hy i).choose)).choose_spec,
      (P.exists_root_eq_smul_of_mem_weylGroup hy i).choose_spec, mul_smul]

@[simp]
lemma weylGroupToPerm_apply_reflection :
    P.weylGroupToPerm ⟨P.reflection i, P.reflection_mem_weylGroup i⟩ = P.reflection_perm i := by
  ext j
  apply P.root.injective
  rw [weylGroupToPerm, MonoidHom.coe_mk, OneHom.coe_mk, Equiv.coe_fn_mk, root_reflection_perm,
    (P.exists_root_eq_smul_of_mem_weylGroup (P.reflection_mem_weylGroup i) j).choose_spec,
    LinearEquiv.smul_def]

@[simp]
lemma range_weylGroupToPerm :
    P.weylGroupToPerm.range = Subgroup.closure (range P.reflection_perm) := by
  refine (Subgroup.closure_eq_of_le _ ?_ ?_).symm
  · rintro - ⟨i, rfl⟩
    simpa only [← weylGroupToPerm_apply_reflection] using mem_range_self _
  · rintro - ⟨⟨w, hw⟩, rfl⟩
    induction hw using Subgroup.closure_induction'' with
    | one =>
      change P.weylGroupToPerm 1 ∈ _
      simpa only [map_one] using Subgroup.one_mem _
    | mem w' hw' =>
      obtain ⟨i, rfl⟩ := hw'
      simpa only [weylGroupToPerm_apply_reflection] using Subgroup.subset_closure (mem_range_self i)
    | inv_mem w' hw' =>
      obtain ⟨i, rfl⟩ := hw'
      simpa only [reflection_inv, weylGroupToPerm_apply_reflection] using
        Subgroup.subset_closure (mem_range_self i)
    | mul w₁ w₂ hw₁ hw₂ h₁ h₂ =>
      simpa only [← Submonoid.mk_mul_mk _ w₁ w₂ hw₁ hw₂, map_mul] using Subgroup.mul_mem _ h₁ h₂

lemma pairing_smul_root_eq (k : ι) (hij : P.reflection_perm i = P.reflection_perm j) :
    P.pairing k i • P.root i = P.pairing k j • P.root j := by
  have h : P.reflection i (P.root k) = P.reflection j (P.root k) := by
    simp only [← root_reflection_perm, hij]
  simpa only [reflection_apply_root, sub_right_inj] using h

lemma pairing_smul_coroot_eq (k : ι) (hij : P.reflection_perm i = P.reflection_perm j) :
    P.pairing i k • P.coroot i = P.pairing j k • P.coroot j := by
  have h : P.coreflection i (P.coroot k) = P.coreflection j (P.coroot k) := by
    simp only [← coroot_reflection_perm, hij]
  simpa only [coreflection_apply_coroot, sub_right_inj] using h

lemma two_nsmul_reflection_eq_of_perm_eq (hij : P.reflection_perm i = P.reflection_perm j) :
    2 • ⇑(P.reflection i) = 2 • P.reflection j := by
  ext x
  suffices 2 • P.toLin x (P.coroot i) • P.root i = 2 • P.toLin x (P.coroot j) • P.root j by
    simpa [reflection_apply]
  calc 2 • P.toLin x (P.coroot i) • P.root i
      = P.toLin x (P.coroot i) • ((2 : R) • P.root i) := ?_
    _ = P.toLin x (P.coroot i) • (P.pairing i j • P.root j) := ?_
    _ = P.toLin x (P.pairing i j • P.coroot i) • (P.root j) := ?_
    _ = P.toLin x ((2 : R) • P.coroot j) • (P.root j) := ?_
    _ = 2 • P.toLin x (P.coroot j) • P.root j := ?_
  · rw [smul_comm, ← Nat.cast_smul_eq_nsmul R, Nat.cast_ofNat]
  · rw [P.pairing_smul_root_eq j i i hij.symm, pairing_same]
  · rw [← smul_comm, ← smul_assoc, map_smul]
  · rw [← P.pairing_smul_coroot_eq j i j hij.symm, pairing_same]
  · rw [map_smul, smul_assoc, ← Nat.cast_smul_eq_nsmul R, Nat.cast_ofNat]

lemma reflection_perm_eq_reflection_perm_iff_of_isSMulRegular (h2 : IsSMulRegular M 2) :
    P.reflection_perm i = P.reflection_perm j ↔ P.reflection i = P.reflection j := by
  refine ⟨fun h ↦ ?_, fun h ↦ Equiv.ext fun k ↦ P.root.injective <| by simp [h]⟩
  suffices ⇑(P.reflection i) = ⇑(P.reflection j) from DFunLike.coe_injective this
  replace h2 : IsSMulRegular (M → M) 2 := IsSMulRegular.pi fun _ ↦ h2
  exact h2 <| P.two_nsmul_reflection_eq_of_perm_eq i j h

lemma reflection_perm_eq_reflection_perm_iff_of_span :
    P.reflection_perm i = P.reflection_perm j ↔
    ∀ x ∈ span R (range P.root), P.reflection i x = P.reflection j x := by
  refine ⟨fun h x hx ↦ ?_, fun h ↦ ?_⟩
  · induction hx using Submodule.span_induction' with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      simp only [← root_reflection_perm, h]
    | zero => simp
    | add x _ y _ hx hy => simp [hx, hy]
    | smul t x _ hx => simp [hx]
  · ext k
    apply P.root.injective
    simp [h (P.root k) (Submodule.subset_span <| mem_range_self k)]

lemma _root_.RootSystem.reflection_perm_eq_reflection_perm_iff (P : RootSystem ι R M N) (i j : ι) :
    P.reflection_perm i = P.reflection_perm j ↔ P.reflection i = P.reflection j := by
  refine ⟨fun h ↦ ?_, fun h ↦ Equiv.ext fun k ↦ P.root.injective <| by simp [h]⟩
  ext x
  exact (reflection_perm_eq_reflection_perm_iff_of_span P.toRootPairing i j).mp h x <| by simp

section pairs

variable (j : ι)

/-- The Coxeter Weight of a pair gives the weight of an edge in a Coxeter diagram, when it is
finite.  It is `4 cos² θ`, where `θ` describes the dihedral angle between hyperplanes. -/
def coxeterWeight : R := pairing P i j * pairing P j i

lemma coxeterWeight_swap : coxeterWeight P i j = coxeterWeight P j i := by
  simp only [coxeterWeight, mul_comm]

/-- Two roots are orthogonal when they are fixed by each others' reflections. -/
def IsOrthogonal : Prop := pairing P i j = 0 ∧ pairing P j i = 0

lemma isOrthogonal.symm : IsOrthogonal P i j ↔ IsOrthogonal P j i := by
  simp only [IsOrthogonal, and_comm]

lemma isOrthogonal_comm (h : IsOrthogonal P i j) : Commute (P.reflection i) (P.reflection j) := by
  rw [Commute, SemiconjBy]
  ext v
  replace h : P.pairing i j = 0 ∧ P.pairing j i = 0 := by simpa [IsOrthogonal] using h
  erw [LinearMap.mul_apply, LinearMap.mul_apply]
  simp only [LinearEquiv.coe_coe, reflection_apply, map_sub, map_smul, root_coroot_eq_pairing,
    zero_smul, sub_zero, h]
  abel

lemma reflection_smul_root_plus_pairing_smul_root (a b : R) :
    P.reflection j (a • P.root i + b • (P.pairing i j) • P.root j) =
      a • P.root i - (a + b) • (P.pairing i j) • P.root j := by
  rw [map_add, LinearMapClass.map_smul, reflection_apply_root, smul_sub, LinearMapClass.map_smul,
    LinearMapClass.map_smul, reflection_apply_self, smul_neg, sub_add, sub_right_inj, add_smul,
    smul_neg, sub_neg_eq_add]

lemma reflection_reflection_smul_root_plus_pairing_smul_root (a b : R) :
    P.reflection i (P.reflection j (a • P.root i + b • (P.pairing i j) • P.root j)) =
      ((a + b) * P.coxeterWeight i j - a) • P.root i - (a + b) • (P.pairing i j) • P.root j := by
  rw [reflection_smul_root_plus_pairing_smul_root, map_sub, map_smul, map_smul, map_smul,
    reflection_apply_self, reflection_apply_root, smul_sub, smul_sub, sub_smul,
    smul_smul (P.pairing i j), ← coxeterWeight, smul_neg, mul_smul]
  abel

end pairs

end RootPairing

section Construction

namespace Bilinear

variable {R M}

/-- A vector `x` is reflective with respect to a bilinear form if multiplication by its norm is
injective, and for any other vector `y`, there is a scalar that takes the norm of `x` to twice the
inner product of `x` and `y`. These conditions are what we need when describing reflection as a map
taking `y` to `y - 2 • (B x y) / (B x x) • x`. -/
def IsReflective (B : M →ₗ[R] M →ₗ[R] R) (x : M) : Prop :=
    IsRegular (B x x) ∧ ∀y : M, ∃r : R, B x x * r = 2 * B x y

/-- The coroot attached to a reflective vector. -/
def coroot_of_reflective (B : M →ₗ[R] M →ₗ[R] R) {x : M} (hx : IsReflective B x) :
    M →ₗ[R] R where
  toFun y := (hx.2 y).choose
  map_add' a b := by
    refine hx.1.1 ?_
    simp only
    rw [(hx.2 (a + b)).choose_spec, mul_add, (hx.2 a).choose_spec, (hx.2 b).choose_spec, map_add,
      mul_add]
  map_smul' r a := by
    refine hx.1.1 ?_
    simp only [RingHom.id_apply]
    rw [(hx.2 (r • a)).choose_spec, smul_eq_mul, mul_left_comm, (hx.2 a).choose_spec, map_smul,
      two_mul, smul_eq_mul, two_mul, mul_add]

@[simp]
lemma coroot_of_reflective_apply (B : M →ₗ[R] M →ₗ[R] R) {x y : M} (hx : IsReflective B x) :
    B x x * coroot_of_reflective B hx y = 2 * B x y := by
  dsimp [coroot_of_reflective]
  rw [(hx.2 y).choose_spec]

@[simp]
lemma coroot_of_reflective_apply_self (B : M →ₗ[R] M →ₗ[R] R) {x : M} (hx : IsReflective B x) :
    coroot_of_reflective B hx x = 2 := by
  refine hx.1.1 ?_
  dsimp only
  rw [coroot_of_reflective_apply B hx, mul_two, two_mul]

lemma reflection_reflective_vector (B : M →ₗ[R] M →ₗ[R] R) {x y : M}
    (hx : IsReflective B x) : Module.reflection (coroot_of_reflective_apply_self B hx) y =
    y - (coroot_of_reflective B hx y) • x :=
  rfl

lemma bilinear_apply_reflection_reflective_vector (B : M →ₗ[R] M →ₗ[R] R) (hSB : LinearMap.IsSymm B)
    {x y z : M} (hx : IsReflective B x) :
    B (Module.reflection (coroot_of_reflective_apply_self B hx) y)
      (Module.reflection (coroot_of_reflective_apply_self B hx) z) = B y z := by
  rw [reflection_reflective_vector, LinearMap.map_sub₂, LinearMap.map_smul₂,
    reflection_reflective_vector, LinearMap.map_sub, LinearMap.map_sub, LinearMap.map_smul]
  refine hx.1.1 ?_
  simp only [smul_eq_mul, map_smul, mul_sub, ← mul_assoc, coroot_of_reflective_apply]
  rw [sub_eq_iff_eq_add, ← hSB x y, RingHom.id_apply, mul_assoc _ _ (B x x), mul_comm _ (B x x),
    coroot_of_reflective_apply]
  ring

lemma reflective_reflection_reflective (B : M →ₗ[R] M →ₗ[R] R) (hSB : LinearMap.IsSymm B) {x y : M}
    (hx : IsReflective B x) (hy : IsReflective B y) :
    IsReflective B (Module.reflection (coroot_of_reflective_apply_self B hx) y) := by
  constructor
  · rw [bilinear_apply_reflection_reflective_vector B hSB]
    exact hy.1
  · intro z
    have hz : Module.reflection (coroot_of_reflective_apply_self B hx)
        (Module.reflection (coroot_of_reflective_apply_self B hx) z) = z := by
      exact
        (LinearEquiv.eq_symm_apply (Module.reflection (coroot_of_reflective_apply_self B hx))).mp
          rfl
    rw [← hz, bilinear_apply_reflection_reflective_vector B hSB,
      bilinear_apply_reflection_reflective_vector B hSB]
    exact hy.2 _

@[simp]
lemma flip_toLin_apply [IsReflexive R M] (B : M →ₗ[R] M →ₗ[R] R) {x y : M} (hx : IsReflective B x) :
    (IsReflexive.toPerfectPairingDual.flip.toLin (R := R) y) (coroot_of_reflective B hx) =
    (coroot_of_reflective B hx) y :=
  rfl

/-- The root pairing given by all reflective vectors for a bilinear form. -/
def of_Bilinear [IsReflexive R M] (B : M →ₗ[R] M →ₗ[R] R) (hNB : LinearMap.Nondegenerate B)
    (hSB : LinearMap.IsSymm B) (h2 : IsRegular (2 : R)) :
    RootPairing {x : M | IsReflective B x} R M (Dual R M) where
  toPerfectPairing := (IsReflexive.toPerfectPairingDual (R := R) (M := M)).flip
  root := Embedding.subtype fun x ↦ IsReflective B x
  coroot :=
  {
    toFun := fun x => coroot_of_reflective B x.2
    inj' := by
      intro x y hxy
      simp only [mem_setOf_eq] at hxy -- x* = y*
      have h1 : ∀ z, coroot_of_reflective B x.2 z = coroot_of_reflective B y.2 z :=
        fun z => congrFun (congrArg DFunLike.coe hxy) z
      have h2x : ∀ z, B x x * coroot_of_reflective B x.2 z =
          B x x * coroot_of_reflective B y.2 z :=
        fun z => congrArg (HMul.hMul ((B x) x)) (h1 z)
      have h2y : ∀ z, B y y * coroot_of_reflective B x.2 z =
          B y y * coroot_of_reflective B y.2 z :=
        fun z => congrArg (HMul.hMul ((B y) y)) (h1 z)
      simp_rw [coroot_of_reflective_apply B x.2] at h2x -- 2(x,z) = (x,x)y*(z)
      simp_rw [coroot_of_reflective_apply B y.2] at h2y -- (y,y)x*(z) = 2(y,z)
      have h2xy : B x x = B y y := by
        refine h2.1 ?_
        dsimp only
        specialize h2x y
        rw [coroot_of_reflective_apply_self] at h2x
        specialize h2y x
        rw [coroot_of_reflective_apply_self] at h2y
        rw [mul_comm, ← h2x, ← hSB, RingHom.id_apply, ← h2y, mul_comm]
      rw [Subtype.ext_iff_val, ← sub_eq_zero]
      refine hNB.1 _ (fun z => ?_)
      rw [map_sub, LinearMap.sub_apply, sub_eq_zero]
      refine h2.1 ?_
      dsimp only
      rw [h2x z, ← h2y z, hxy, h2xy] }
  root_coroot_two := by
    intro x
    dsimp only [coe_setOf, Embedding.coe_subtype, mem_setOf_eq, id_eq, eq_mp_eq_cast,
      RingHom.id_apply, eq_mpr_eq_cast, cast_eq, Embedding.coeFn_mk]
    rw [flip_toLin_apply, coroot_of_reflective_apply_self B x.2]
  reflection_perm := fun x =>
    { toFun := fun y => ⟨(Module.reflection (coroot_of_reflective_apply_self B x.2) y),
        reflective_reflection_reflective B hSB x.2 y.2⟩
      invFun := fun y => ⟨(Module.reflection (coroot_of_reflective_apply_self B x.2) y),
        reflective_reflection_reflective B hSB x.2 y.2⟩
      left_inv := by
        intro y
        simp [involutive_reflection (coroot_of_reflective_apply_self B x.2) y]
      right_inv := by
        intro y
        simp [involutive_reflection (coroot_of_reflective_apply_self B x.2) y] }
  reflection_perm_root := by
    intro x y
    simp only [coe_setOf, Embedding.coe_subtype, mem_setOf_eq, Embedding.coeFn_mk, Equiv.coe_fn_mk]
    rw [reflection_reflective_vector B x.2, flip_toLin_apply]
  reflection_perm_coroot := by
    intro x y
    simp only [coe_setOf, mem_setOf_eq, Embedding.coeFn_mk, Embedding.coe_subtype, flip_toLin_apply,
      Equiv.coe_fn_mk]
    ext z
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
    refine y.2.1.1 ?_
    simp only [mem_setOf_eq, mul_sub, ← mul_assoc, coroot_of_reflective_apply B y.2]
    rw [← bilinear_apply_reflection_reflective_vector B hSB x.2 (z := y),
      coroot_of_reflective_apply, ← hSB z, ← hSB z, RingHom.id_apply, RingHom.id_apply,
      reflection_reflective_vector, map_sub, map_smul, mul_sub, sub_eq_sub_iff_comm, sub_left_inj]
    refine x.2.1.1 ?_
    simp only [mem_setOf_eq, smul_eq_mul]
    rw [mul_left_comm, coroot_of_reflective_apply B x.2, mul_left_comm (B x x), ← mul_assoc (B x x),
    coroot_of_reflective_apply B x.2, ← hSB x y, RingHom.id_apply, ← hSB x z, RingHom.id_apply]
    ring

end Bilinear

end Construction

section BaseChange

variable {S : Type*} [CommRing S] [Algebra R S] (P : RootPairing ι R M N)
/-!
/-- The base change of a root pairing. -/
def baseChange : RootPairing ι S (S ⊗[R] M) (S ⊗[R] N) :=
  { P.toPerfectPairing.baseChange with
    root := P.root
    coroot := P.coroot
    root_coroot_two := P.root_coroot_two
    mapsTo_preReflection_root := P.mapsTo_preReflection_root
    mapsTo_preReflection_coroot := P.mapsTo_preReflection_coroot }
-/

end BaseChange
