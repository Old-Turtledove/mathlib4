/-
Copyright (c) 2024 Damien Thomine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damien Thomine, Pietro Monticone
-/
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.OmegaCompletePartialOrder
import Mathlib.Topology.UniformSpace.UniformConvergenceTopology

/-!
# Dynamical entourages
Bowen-Dinaburg's definition of topological entropy of a transformation `T` in a metric space
`(X, d)` relies on the so-called dynamical balls. These balls are sets
`B (x, ε, n) = { y | ∀ k < n, d(T^[k] x, T^[k] y) < ε }`.

We implement Bowen-Dinaburg's definitions in the more general context of uniform spaces. Dynamical
balls are replaced by what we call dynamical entourages. This file collects all general lemmas
about these objects.

## Main definitions
- `dynEntourage`: dynamical entourage associated with a given transformation `T`, entourage `U`
and time `n`.

## Tags
entropy

## TODO
Once #PR14718 has passed, add product of entourages.

In the context of (pseudo-e)metric spaces, relate the usual definition of dynamical balls with
these dynamical entourages.
-/

namespace Dynamics

open Prod Set Uniformity UniformSpace UniformConvergence

/-! ### Pi entourages -/

/-- Pi entourages-/
lemma UniformFun.mem_ball_gen {α β : Type*} (U : Set (β × β)) (f g : α →ᵤ β) :
  g ∈ ball f (UniformFun.gen α β U) ↔  ∀ i : α, (f i, g i) ∈ U := by rfl

lemma UniformFun.idRel_subset_gen (α : Type*) {β : Type*} {U : Set (β × β)} (h : idRel ⊆ U) :
    idRel ⊆ UniformFun.gen α β U := by
  intro (f, g) f_g
  rw [mem_idRel] at f_g
  rw [UniformFun.mem_gen, f_g]
  exact fun i ↦ h (mem_idRel.2 (Eq.refl (g i)))

lemma UniformFun.comp_gen_subset (α : Type*) {β : Type*} (U V : Set (β × β)) :
    (UniformFun.gen α β U) ○ (UniformFun.gen α β V) ⊆ UniformFun.gen α β (U ○ V) := by
  intro (f, g)
  simp only [compRel, UniformFun.mem_gen, mem_setOf_eq, forall_exists_index, and_imp]
  exact fun h f_h h_g i ↦ ⟨h i, ⟨f_h i, h_g i⟩⟩

lemma _root_.SymmetricRel.uniformFun_gen (α : Type*) {β : Type*} {U : Set (β × β)}
    (U_symm : SymmetricRel U) :
    SymmetricRel (UniformFun.gen α β U) := by
  ext fg
  rw [mem_preimage, UniformFun.mem_gen, UniformFun.mem_gen, fst_swap, snd_swap]
  exact Iff.of_eq (forall_congr fun i ↦ eq_iff_iff.2 U_symm.mk_mem_comm)

/-! ### Dynamical entourages -/

/-- Another definition of dynamical entourages.-/
def dynEntourage' {X : Type*} (T : X → X) (U : Set (X × X)) (n : ℕ) : Set (X × X) :=
  {(x, y) : X × X | (fun k : Fin n ↦ T^[k] x, fun k : Fin n ↦ T^[k] y) ∈ UniformFun.gen (Fin n) X U}

lemma mem_dynEntourage' {X : Type*} {T : X → X} {U : Set (X × X)} {n : ℕ} {x y : X} :
    (x, y) ∈ dynEntourage' T U n ↔ ∀ k < n, (T^[k] x, T^[k] y) ∈ U := by
  simp [dynEntourage']
  rw [UniformFun.mem_gen]
  rw [← UniformFun.toFun_ofFun (fun k : Fin n ↦ T^[k] x)]
  sorry

lemma mem_ball_dynEntourage' {X : Type*} {T : X → X} {U : Set (X × X)} {n : ℕ} {x y : X} :
    y ∈ ball x (dynEntourage' T U n) ↔ ∀ k < n, T^[k] y ∈ ball (T^[k] x) U := by
  simp only [ball, mem_preimage]; exact mem_dynEntourage'

lemma idRel_subset_dynEntourage' {X : Type*} (T : X → X) {U : Set (X × X)} (h : idRel ⊆ U) (n : ℕ) :
    idRel ⊆ dynEntourage' T U n := by
  simp only [dynEntourage', idRel_subset, mem_setOf_eq]
  exact fun _ ↦ UniformFun.idRel_subset_gen (Fin n) h (mem_idRel.2 (Eq.refl _))

lemma _root_.SymmetricRel.dynEntourage' {X : Type*} (T : X → X) {U : Set (X × X)}
    (h : SymmetricRel U) (n : ℕ) :
    SymmetricRel (dynEntourage' T U n) := by
  ext xy
  simp only [Dynamics.dynEntourage', preimage_setOf_eq, fst_swap, snd_swap, mem_setOf_eq]
  exact (h.uniformFun_gen (Fin n)).mk_mem_comm







end Dynamics

#lint

/--
/-- The dynamical entourage associated to a transformation `T`, entourage `U` and time `n`
is the set of points `(x, y)` such that `(T^[k] x, T^[k] y) ∈ U` for all `k < n`, i.e.
which are `U`-close up to time `n`.-/
def dynEntourage (T : X → X) (U : Set (X × X)) (n : ℕ) : Set (X × X) :=
  ⋂ k < n, (map T T)^[k] ⁻¹' U

lemma dynEntourage_eq_inter_Ico (T : X → X) (U : Set (X × X)) (n : ℕ) :
    dynEntourage T U n = ⋂ k : Ico 0 n, (map T T)^[k] ⁻¹' U := by
  simp [dynEntourage]

lemma mem_dynEntourage {T : X → X} {U : Set (X × X)} {n : ℕ} {x y : X} :
    (x, y) ∈ dynEntourage T U n ↔ ∀ k < n, (T^[k] x, T^[k] y) ∈ U := by
  simp [dynEntourage]

lemma mem_ball_dynEntourage {T : X → X} {U : Set (X × X)} {n : ℕ} {x y : X} :
    y ∈ ball x (dynEntourage T U n) ↔ ∀ k < n, T^[k] y ∈ ball (T^[k] x) U := by
  simp only [ball, mem_preimage]; exact mem_dynEntourage

lemma dynEntourage_mem_uniformity [UniformSpace X] {T : X → X} (h : UniformContinuous T)
    {U : Set (X × X)} (U_uni : U ∈ 𝓤 X) (n : ℕ) :
    dynEntourage T U n ∈ 𝓤 X := by
  rw [dynEntourage_eq_inter_Ico T U n]
  refine Filter.iInter_mem.2 fun k ↦ ?_
  rw [map_iterate T T k]
  exact uniformContinuous_def.1 (UniformContinuous.iterate T k h) U U_uni

lemma idRel_subset_dynEntourage (T : X → X) {U : Set (X × X)} (h : idRel ⊆ U) (n : ℕ) :
    idRel ⊆ (dynEntourage T U n) := by
  simp only [dynEntourage, map_iterate, subset_iInter_iff, idRel_subset, mem_preimage, map_apply]
  exact fun _ _ _ ↦ h rfl

lemma _root_.SymmetricRel.dynEntourage (T : X → X) {U : Set (X × X)} (h : SymmetricRel U) (n : ℕ) :
    SymmetricRel (dynEntourage T U n) := by
  ext xy
  simp only [Dynamics.dynEntourage, map_iterate, mem_preimage, mem_iInter]
  refine forall₂_congr fun k _ ↦ ?_
  exact map_apply' _ _ _ ▸ SymmetricRel.mk_mem_comm h

lemma dynEntourage_comp_subset (T : X → X) (U V : Set (X × X)) (n : ℕ) :
    (dynEntourage T U n) ○ (dynEntourage T V n) ⊆ dynEntourage T (U ○ V) n := by
  simp only [dynEntourage, map_iterate, subset_iInter_iff]
  intro k k_n xy xy_comp
  simp only [compRel, mem_iInter, mem_preimage, map_apply, mem_setOf_eq] at xy_comp ⊢
  rcases xy_comp with ⟨z, hz1, hz2⟩
  exact mem_ball_comp (hz1 k k_n) (hz2 k k_n)

lemma _root_.isOpen.dynEntourage [TopologicalSpace X] {T : X → X} (T_cont : Continuous T)
    {U : Set (X × X)} (U_open : IsOpen U) (n : ℕ) :
    IsOpen (dynEntourage T U n) := by
  rw [dynEntourage_eq_inter_Ico T U n]
  refine isOpen_iInter_of_finite fun k ↦ ?_
  exact continuous_def.1 ((T_cont.prod_map T_cont).iterate k) U U_open

lemma dynEntourage_monotone (T : X → X) (n : ℕ) :
    Monotone (fun U : Set (X × X) ↦ dynEntourage T U n) :=
  fun _ _ h ↦ iInter₂_mono fun _ _ ↦ preimage_mono h

lemma dynEntourage_antitone (T : X → X) (U : Set (X × X)) :
    Antitone (fun n : ℕ ↦ dynEntourage T U n) :=
  fun m n m_n ↦ iInter₂_mono' fun k k_m ↦ by use k, lt_of_lt_of_le k_m m_n

@[simp]
lemma dynEntourage_zero {T : X → X} {U : Set (X × X)} :
    dynEntourage T U 0 = univ := by simp [dynEntourage]

@[simp]
lemma dynEntourage_one {T : X → X} {U : Set (X × X)} :
    dynEntourage T U 1 = U := by simp [dynEntourage]

@[simp]
lemma dynEntourage_univ {T : X → X} {n : ℕ} :
    dynEntourage T univ n = univ := by simp [dynEntourage]

lemma mem_ball_dynEntourage_comp (T : X → X) (n : ℕ) {U : Set (X × X)} (U_symm : SymmetricRel U)
    (x y : X) (h : (ball x (dynEntourage T U n) ∩ ball y (dynEntourage T U n)).Nonempty) :
    x ∈ ball y (dynEntourage T (U ○ U) n) := by
  rcases h with ⟨z, z_Bx, z_By⟩
  rw [mem_ball_symmetry (SymmetricRel.dynEntourage T U_symm n)] at z_Bx
  exact dynEntourage_comp_subset T U U n (mem_ball_comp z_By z_Bx)

lemma _root_.Function.Semiconj.preimage_dynEntourage {Y : Type*} {S : X → X} {T : Y → Y} {φ : X → Y}
    (h : Function.Semiconj φ S T) (U : Set (Y × Y)) (n : ℕ) :
    (map φ φ)⁻¹' (dynEntourage T U n) = dynEntourage S ((map φ φ)⁻¹' U) n := by
  rw [dynEntourage, preimage_iInter₂]
  refine iInter₂_congr fun k _ ↦ ?_
  rw [← preimage_comp, ← preimage_comp, map_iterate S S k, map_iterate T T k, map_comp_map,
    map_comp_map, (Function.Semiconj.iterate_right h k).comp_eq]

lemma dynEntourage_entourageProd {Y : Type*} (S : X → X) (T : Y → Y) (U : Set (X × X))
    (V : Set (Y × Y)) (n : ℕ) :
    dynEntourage (map S T) (entourageProd U V) n =
    entourageProd (dynEntourage S U n) (dynEntourage T V n) := by
  ext x
  rw [entourageProd, entourageProd, mem_dynEntourage]
  simp only [mem_dynEntourage, mem_setOf_eq, map_iterate, map_fst, map_snd]
  exact forall₂_and
-/
