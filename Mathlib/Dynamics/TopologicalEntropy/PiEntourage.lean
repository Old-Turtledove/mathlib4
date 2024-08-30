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
    (UniformFun.gen α β U) ○ (UniformFun.gen α β V) = UniformFun.gen α β (U ○ V) := by
  classical
  ext fg
  rcases isEmpty_or_nonempty β with b_emp | b_nemp
  · rcases isEmpty_or_nonempty α with a_emp | a_nemp
    · simp only [compRel, UniformFun.gen, IsEmpty.forall_iff, mem_setOf_eq, iff_true, true_and]
      use fg.1
    · have := isEmpty_iff.2 fun f ↦ isEmpty_iff.1 (isEmpty_fun.2 ⟨a_nemp, b_emp⟩)
        (UniformFun.toFun f)
      simp only [eq_empty_of_isEmpty]
  simp only [compRel, UniformFun.gen, mem_setOf_eq]
  apply Iff.intro <;> intro hyp
  · rcases hyp with ⟨h, h_f, h_g⟩
    exact fun i ↦ ⟨h i, ⟨h_f i, h_g i⟩⟩
  · choose! h h_fg using hyp
    exact ⟨h, ⟨fun i ↦ (h_fg i).1, fun i ↦ (h_fg i).2⟩⟩

lemma _root_.SymmetricRel.uniformFun_gen (α : Type*) {β : Type*} {U : Set (β × β)}
    (U_symm : SymmetricRel U) :
    SymmetricRel (UniformFun.gen α β U) := by
  ext fg
  rw [mem_preimage, UniformFun.mem_gen, UniformFun.mem_gen, fst_swap, snd_swap]
  exact Iff.of_eq (forall_congr fun i ↦ eq_iff_iff.2 U_symm.mk_mem_comm)

/-! ### Dynamical entourages -/

variable {X : Type*}

/-- Another definition of dynamical entourages.-/
def dynEntourage' (T : X → X) (U : Set (X × X)) (n : ℕ) : Set (X × X) :=
  {(x, y) : X × X | (UniformFun.ofFun fun k : Fin n ↦ T^[k] x,
    UniformFun.ofFun fun k : Fin n ↦ T^[k] y) ∈ UniformFun.gen (Fin n) X U}

lemma mem_dynEntourage'_def {T : X → X} {U : Set (X × X)} {n : ℕ} {x y : X} :
    (x, y) ∈ dynEntourage' T U n ↔ (UniformFun.ofFun fun k : Fin n ↦ T^[k] x,
    UniformFun.ofFun fun k : Fin n ↦ T^[k] y) ∈ UniformFun.gen (Fin n) X U := by rfl

lemma mem_dynEntourage' {T : X → X} {U : Set (X × X)} {n : ℕ} {x y : X} :
    (x, y) ∈ dynEntourage' T U n ↔ ∀ k < n, (T^[k] x, T^[k] y) ∈ U := by
  simp only [dynEntourage', UniformFun.mem_gen, UniformFun.toFun_ofFun, mem_setOf_eq]
  exact Fin.forall_iff

lemma dynEntourage'_eq_iInter {T : X → X} {U : Set (X × X)} {n : ℕ} :
    dynEntourage' T U n = ⋂ k : Fin n, (map T T)^[k] ⁻¹' U := by
  ext xy
  rw [mem_dynEntourage', mem_iInter, Fin.forall_iff]
  simp only [map_iterate, mem_preimage]
  rfl

lemma mem_ball_dynEntourage' {T : X → X} {U : Set (X × X)} {n : ℕ} {x y : X} :
    y ∈ ball x (dynEntourage' T U n) ↔ ∀ k < n, T^[k] y ∈ ball (T^[k] x) U := by
  simp only [ball, mem_preimage]
  exact mem_dynEntourage'

lemma idRel_subset_dynEntourage' (T : X → X) {U : Set (X × X)} (h : idRel ⊆ U) (n : ℕ) :
    idRel ⊆ dynEntourage' T U n := by
  simp only [dynEntourage', idRel_subset, mem_setOf_eq]
  exact fun _ ↦ UniformFun.idRel_subset_gen (Fin n) h (mem_idRel.2 (Eq.refl _))

lemma _root_.SymmetricRel.dynEntourage' (T : X → X) {U : Set (X × X)}
    (h : SymmetricRel U) (n : ℕ) :
    SymmetricRel (dynEntourage' T U n) := by
  ext xy
  simp only [Dynamics.dynEntourage', preimage_setOf_eq, fst_swap, snd_swap, mem_setOf_eq]
  exact (h.uniformFun_gen (Fin n)).mk_mem_comm

lemma dynEntourage'_comp_subset (T : X → X) (U V : Set (X × X)) (n : ℕ) :
    (dynEntourage' T U n) ○ (dynEntourage' T V n) ⊆ dynEntourage' T (U ○ V) n := by
  intro (x, y) h
  rcases mem_compRel.1 h with ⟨z, x_z, z_y⟩
  rw [mem_dynEntourage'_def] at x_z z_y ⊢
  rw [← UniformFun.comp_gen_subset]
  exact mem_compRel.2 ⟨UniformFun.ofFun fun k : Fin n ↦ T^[k] z, ⟨x_z, z_y⟩⟩

lemma dynEntourage'_mem_uniformity [UniformSpace X] {T : X → X} (h : UniformContinuous T)
    {U : Set (X × X)} (U_uni : U ∈ 𝓤 X) (n : ℕ) :
    dynEntourage' T U n ∈ 𝓤 X := by
  rw [dynEntourage'_eq_iInter]
  refine Filter.iInter_mem.2 fun k ↦ ?_
  rw [map_iterate T T k]
  exact uniformContinuous_def.1 (UniformContinuous.iterate T k h) U U_uni

lemma _root_.isOpen.dynEntourage [TopologicalSpace X] {T : X → X} (T_cont : Continuous T)
    {U : Set (X × X)} (U_open : IsOpen U) (n : ℕ) :
    IsOpen (dynEntourage' T U n) := by
  rw [dynEntourage'_eq_iInter]
  refine isOpen_iInter_of_finite fun k ↦ ?_S
  exact continuous_def.1 ((T_cont.prod_map T_cont).iterate k) U U_open

/--
lemma dynEntourage_monotone (T : X → X) (n : ℕ) :
    Monotone (fun U : Set (X × X) ↦ dynEntourage' T U n) := by
  intro U V U_V
  simp only
  fun _ _ h ↦ iInter₂_mono fun _ _ ↦ preimage_mono h

lemma dynEntourage_antitone (T : X → X) (U : Set (X × X)) :
    Antitone (fun n : ℕ ↦ dynEntourage' T U n) :=
  fun m n m_n ↦ iInter₂_mono' fun k k_m ↦ by use k, lt_of_lt_of_le k_m m_n
-/

@[simp]
lemma dynEntourage_zero {T : X → X} {U : Set (X × X)} :
    dynEntourage' T U 0 = univ := by simp [dynEntourage']

@[simp]
lemma dynEntourage_one {T : X → X} {U : Set (X × X)} :
    dynEntourage' T U 1 = U := by simp [dynEntourage']

@[simp]
lemma dynEntourage_univ {T : X → X} {n : ℕ} :
    dynEntourage' T univ n = univ := by simp [dynEntourage']

lemma mem_ball_dynEntourage_comp (T : X → X) (n : ℕ) {U : Set (X × X)} (U_symm : SymmetricRel U)
    (x y : X) (h : (ball x (dynEntourage' T U n) ∩ ball y (dynEntourage' T U n)).Nonempty) :
    x ∈ ball y (dynEntourage' T (U ○ U) n) := by
  rcases h with ⟨z, z_Bx, z_By⟩
  rw [mem_ball_symmetry (U_symm.dynEntourage' T n)] at z_Bx
  exact dynEntourage'_comp_subset T U U n (mem_ball_comp z_By z_Bx)

lemma _root_.Function.Semiconj.preimage_dynEntourage {Y : Type*} {S : X → X} {T : Y → Y} {φ : X → Y}
    (h : Function.Semiconj φ S T) (U : Set (Y × Y)) (n : ℕ) :
    (map φ φ)⁻¹' (dynEntourage' T U n) = dynEntourage' S ((map φ φ)⁻¹' U) n := by
  ext xy
  rw [mem_preimage, mem_dynEntourage'_def, mem_dynEntourage'_def]
  simp only [map_fst, map_snd, UniformFun.mem_gen, UniformFun.toFun_ofFun, mem_preimage, map_apply]
  refine Iff.of_eq (forall_congr fun k ↦ ?_)
  rw [(h.iterate_right k).eq xy.1, (h.iterate_right k).eq xy.2]

end Dynamics

#lint
