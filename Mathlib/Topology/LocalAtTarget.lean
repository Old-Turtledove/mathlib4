/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.LocallyClosed

/-!
# Properties of maps that are local at the target.

We show that the following properties of continuous maps are local at the target :
- `IsInducing`
- `Embedding`
- `IsOpenEmbedding`
- `IsClosedEmbedding`

-/


open TopologicalSpace Set Filter

open Topology Filter

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] {f : α → β}
variable {s : Set β} {ι : Type*} {U : ι → Opens β}

theorem Set.restrictPreimage_inducing (s : Set β) (h : IsInducing f) :
    IsInducing (s.restrictPreimage f) := by
  simp_rw [← IsInducing.subtypeVal.of_comp_iff, isInducing_iff_nhds, restrictPreimage,
    MapsTo.coe_restrict, restrict_eq, ← @Filter.comap_comap _ _ _ _ _ f, Function.comp_apply] at h ⊢
  intro a
  rw [← h, ← IsInducing.subtypeVal.nhds_eq_comap]

alias IsInducing.restrictPreimage := Set.restrictPreimage_inducing

theorem Set.restrictPreimage_embedding (s : Set β) (h : IsEmbedding f) :
    Embedding (s.restrictPreimage f) :=
  ⟨h.1.restrictPreimage s, h.2.restrictPreimage s⟩

alias Embedding.restrictPreimage := Set.restrictPreimage_embedding

theorem Set.restrictPreimage_isOpenEmbedding (s : Set β) (h : IsOpenEmbedding f) :
    IsOpenEmbedding (s.restrictPreimage f) :=
  ⟨h.1.restrictPreimage s,
    (s.range_restrictPreimage f).symm ▸ continuous_subtype_val.isOpen_preimage _ h.isOpen_range⟩

alias IsOpenEmbedding.restrictPreimage := Set.restrictPreimage_isOpenEmbedding

theorem Set.restrictPreimage_isClosedEmbedding (s : Set β) (h : IsClosedEmbedding f) :
    IsClosedEmbedding (s.restrictPreimage f) :=
  ⟨h.1.restrictPreimage s,
    (s.range_restrictPreimage f).symm ▸ IsInducing.subtypeVal.isClosed_preimage _ h.isClosed_range⟩

alias IsClosedEmbedding.restrictPreimage := Set.restrictPreimage_isClosedEmbedding

theorem IsClosedMap.restrictPreimage (H : IsClosedMap f) (s : Set β) :
    IsClosedMap (s.restrictPreimage f) := by
  intro t
  suffices ∀ u, IsClosed u → Subtype.val ⁻¹' u = t →
    ∃ v, IsClosed v ∧ Subtype.val ⁻¹' v = s.restrictPreimage f '' t by
      simpa [isClosed_induced_iff]
  exact fun u hu e => ⟨f '' u, H u hu, by simp [← e, image_restrictPreimage]⟩

@[deprecated (since := "2024-04-02")]
theorem Set.restrictPreimage_isClosedMap (s : Set β) (H : IsClosedMap f) :
    IsClosedMap (s.restrictPreimage f) := H.restrictPreimage s

theorem IsOpenMap.restrictPreimage (H : IsOpenMap f) (s : Set β) :
    IsOpenMap (s.restrictPreimage f) := by
  intro t
  suffices ∀ u, IsOpen u → Subtype.val ⁻¹' u = t →
    ∃ v, IsOpen v ∧ Subtype.val ⁻¹' v = s.restrictPreimage f '' t by
      simpa [isOpen_induced_iff]
  exact fun u hu e => ⟨f '' u, H u hu, by simp [← e, image_restrictPreimage]⟩

@[deprecated (since := "2024-04-02")]
theorem Set.restrictPreimage_isOpenMap (s : Set β) (H : IsOpenMap f) :
    IsOpenMap (s.restrictPreimage f) := H.restrictPreimage s

variable (hU : iSup U = ⊤)
include hU

theorem isOpen_iff_inter_of_iSup_eq_top (s : Set β) : IsOpen s ↔ ∀ i, IsOpen (s ∩ U i) := by
  constructor
  · exact fun H i => H.inter (U i).2
  · intro H
    have : ⋃ i, (U i : Set β) = Set.univ := by
      convert congr_arg (SetLike.coe) hU
      simp
    rw [← s.inter_univ, ← this, Set.inter_iUnion]
    exact isOpen_iUnion H

theorem isOpen_iff_coe_preimage_of_iSup_eq_top (s : Set β) :
    IsOpen s ↔ ∀ i, IsOpen ((↑) ⁻¹' s : Set (U i)) := by
  -- Porting note: rewrote to avoid ´simp´ issues
  rw [isOpen_iff_inter_of_iSup_eq_top hU s]
  refine forall_congr' fun i => ?_
  rw [(U _).2.isOpenEmbedding_subtype_val.isOpen_iff_image_isOpen]
  erw [Set.image_preimage_eq_inter_range]
  rw [Subtype.range_coe, Opens.carrier_eq_coe]

theorem isClosed_iff_coe_preimage_of_iSup_eq_top (s : Set β) :
    IsClosed s ↔ ∀ i, IsClosed ((↑) ⁻¹' s : Set (U i)) := by
  simpa using isOpen_iff_coe_preimage_of_iSup_eq_top hU sᶜ

theorem isLocallyClosed_iff_coe_preimage_of_iSup_eq_top (s : Set β) :
    IsLocallyClosed s ↔ ∀ i, IsLocallyClosed ((↑) ⁻¹' s : Set (U i)) := by
  simp_rw [isLocallyClosed_iff_isOpen_coborder]
  rw [isOpen_iff_coe_preimage_of_iSup_eq_top hU]
  exact forall_congr' fun i ↦ by rw [(U i).isOpen.isOpenEmbedding_subtype_val.coborder_preimage]

theorem isOpenMap_iff_isOpenMap_of_iSup_eq_top :
    IsOpenMap f ↔ ∀ i, IsOpenMap ((U i).1.restrictPreimage f) := by
  refine ⟨fun h i => h.restrictPreimage _, ?_⟩
  rintro H s hs
  rw [isOpen_iff_coe_preimage_of_iSup_eq_top hU]
  intro i
  convert H i _ (hs.preimage continuous_subtype_val)
  ext ⟨x, hx⟩
  suffices (∃ y, y ∈ s ∧ f y = x) ↔ ∃ y, y ∈ s ∧ f y ∈ U i ∧ f y = x by
    simpa [Set.restrictPreimage, ← Subtype.coe_inj]
  exact ⟨fun ⟨a, b, c⟩ => ⟨a, b, c.symm ▸ hx, c⟩, fun ⟨a, b, _, c⟩ => ⟨a, b, c⟩⟩

theorem isClosedMap_iff_isClosedMap_of_iSup_eq_top :
    IsClosedMap f ↔ ∀ i, IsClosedMap ((U i).1.restrictPreimage f) := by
  refine ⟨fun h i => h.restrictPreimage _, ?_⟩
  rintro H s hs
  rw [isClosed_iff_coe_preimage_of_iSup_eq_top hU]
  intro i
  convert H i _ ⟨⟨_, hs.1, eq_compl_comm.mpr rfl⟩⟩
  ext ⟨x, hx⟩
  suffices (∃ y, y ∈ s ∧ f y = x) ↔ ∃ y, y ∈ s ∧ f y ∈ U i ∧ f y = x by
    simpa [Set.restrictPreimage, ← Subtype.coe_inj]
  exact ⟨fun ⟨a, b, c⟩ => ⟨a, b, c.symm ▸ hx, c⟩, fun ⟨a, b, _, c⟩ => ⟨a, b, c⟩⟩

theorem inducing_iff_inducing_of_iSup_eq_top (h : Continuous f) :
    IsInducing f ↔ ∀ i, IsInducing ((U i).1.restrictPreimage f) := by
  simp_rw [← IsInducing.subtypeVal.of_comp_iff, isInducing_iff_nhds, restrictPreimage,
    MapsTo.coe_restrict, restrict_eq, ← @Filter.comap_comap _ _ _ _ _ f]
  constructor
  · intro H i x
    rw [Function.comp_apply, ← H, ← IsInducing.subtypeVal.nhds_eq_comap]
  · intro H x
    obtain ⟨i, hi⟩ :=
      Opens.mem_iSup.mp
        (show f x ∈ iSup U by
          rw [hU]
          trivial)
    erw [← IsOpenEmbedding.map_nhds_eq (h.1 _ (U i).2).isOpenEmbedding_subtype_val ⟨x, hi⟩]
    rw [(H i) ⟨x, hi⟩, Filter.subtype_coe_map_comap, Function.comp_apply, Subtype.coe_mk,
      inf_eq_left, Filter.le_principal_iff]
    exact Filter.preimage_mem_comap ((U i).2.mem_nhds hi)

theorem embedding_iff_embedding_of_iSup_eq_top (h : Continuous f) :
    IsEmbedding f ↔ ∀ i, Embedding ((U i).1.restrictPreimage f) := by
  simp_rw [embedding_iff]
  rw [forall_and]
  apply and_congr
  · apply inducing_iff_inducing_of_iSup_eq_top <;> assumption
  · apply Set.injective_iff_injective_of_iUnion_eq_univ
    convert congr_arg SetLike.coe hU
    simp

theorem isOpenEmbedding_iff_isOpenEmbedding_of_iSup_eq_top (h : Continuous f) :
    IsOpenEmbedding f ↔ ∀ i, IsOpenEmbedding ((U i).1.restrictPreimage f) := by
  simp_rw [isOpenEmbedding_iff]
  rw [forall_and]
  apply and_congr
  · apply embedding_iff_embedding_of_iSup_eq_top <;> assumption
  · simp_rw [Set.range_restrictPreimage]
    apply isOpen_iff_coe_preimage_of_iSup_eq_top hU

theorem isClosedEmbedding_iff_isClosedEmbedding_of_iSup_eq_top (h : Continuous f) :
    IsClosedEmbedding f ↔ ∀ i, IsClosedEmbedding ((U i).1.restrictPreimage f) := by
  simp_rw [isClosedEmbedding_iff]
  rw [forall_and]
  apply and_congr
  · apply embedding_iff_embedding_of_iSup_eq_top <;> assumption
  · simp_rw [Set.range_restrictPreimage]
    apply isClosed_iff_coe_preimage_of_iSup_eq_top hU
