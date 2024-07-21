/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Violeta Hernández Palacios
-/
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.SetTheory.Cardinal.Cofinality
import Mathlib.SetTheory.Cardinal.Continuum

/-!
# Cardinal of sigma-algebras

If a sigma-algebra is generated by a set of sets `s`, then the cardinality of the sigma-algebra is
bounded by `(max #s 2) ^ ℵ₀`. This is stated in `MeasurableSpace.cardinal_generate_measurable_le`
and `MeasurableSpace.cardinalMeasurableSet_le`.

In particular, if `#s ≤ 𝔠`, then the generated sigma-algebra has cardinality at most `𝔠`, see
`MeasurableSpace.cardinal_measurableSet_le_continuum`.

For the proof, we rely on an explicit inductive construction of the sigma-algebra generated by
`s` (instead of the inductive predicate `GenerateMeasurable`). This transfinite inductive
construction is parameterized by an ordinal `< ω₁`, and the cardinality bound is preserved along
each step of the construction. We show in `MeasurableSpace.generateMeasurable_eq_rec` that this
indeed generates this sigma-algebra.
-/


universe u

variable {α : Type u}

open Cardinal Set

-- Porting note: fix universe below, not here
local notation "ω₁" => (WellOrder.α <| Quotient.out <| Cardinal.ord (aleph 1 : Cardinal))

namespace MeasurableSpace

/-- Transfinite induction construction of the sigma-algebra generated by a set of sets `s`. At each
step, we add all elements of `s`, the empty set, the complements of already constructed sets, and
countable unions of already constructed sets. We index this construction by an ordinal `< ω₁`, as
this will be enough to generate all sets in the sigma-algebra.

This construction is very similar to that of the Borel hierarchy. -/
def generateMeasurableRec (s : Set (Set α)) : (ω₁ : Type u) → Set (Set α)
  | i =>
    let S := ⋃ j : Iio i, generateMeasurableRec s (j.1)
    s ∪ {∅} ∪ compl '' S ∪ Set.range fun f : ℕ → S => ⋃ n, (f n).1
  termination_by i => i
  decreasing_by exact j.2

theorem self_subset_generateMeasurableRec (s : Set (Set α)) (i : ω₁) :
    s ⊆ generateMeasurableRec s i := by
  unfold generateMeasurableRec
  apply_rules [subset_union_of_subset_left]
  exact subset_rfl

theorem empty_mem_generateMeasurableRec (s : Set (Set α)) (i : ω₁) :
    ∅ ∈ generateMeasurableRec s i := by
  unfold generateMeasurableRec
  exact mem_union_left _ (mem_union_left _ (mem_union_right _ (mem_singleton ∅)))

theorem compl_mem_generateMeasurableRec {s : Set (Set α)} {i j : ω₁} (h : j < i) {t : Set α}
    (ht : t ∈ generateMeasurableRec s j) : tᶜ ∈ generateMeasurableRec s i := by
  unfold generateMeasurableRec
  exact mem_union_left _ (mem_union_right _ ⟨t, mem_iUnion.2 ⟨⟨j, h⟩, ht⟩, rfl⟩)

theorem iUnion_mem_generateMeasurableRec {s : Set (Set α)} {i : ω₁} {f : ℕ → Set α}
    (hf : ∀ n, ∃ j < i, f n ∈ generateMeasurableRec s j) :
    (⋃ n, f n) ∈ generateMeasurableRec s i := by
  unfold generateMeasurableRec
  exact mem_union_right _ ⟨fun n => ⟨f n, let ⟨j, hj, hf⟩ := hf n; mem_iUnion.2 ⟨⟨j, hj⟩, hf⟩⟩, rfl⟩

theorem generateMeasurableRec_subset (s : Set (Set α)) {i j : ω₁} (h : i ≤ j) :
    generateMeasurableRec s i ⊆ generateMeasurableRec s j := fun x hx => by
  rcases eq_or_lt_of_le h with (rfl | h)
  · exact hx
  · convert iUnion_mem_generateMeasurableRec fun _ => ⟨i, h, hx⟩
    exact (iUnion_const x).symm

/-- At each step of the inductive construction, the cardinality bound `≤ (max #s 2) ^ ℵ₀` holds.
-/
theorem cardinal_generateMeasurableRec_le (s : Set (Set α)) (i : ω₁) :
    #(generateMeasurableRec s i) ≤ max #s 2 ^ aleph0.{u} := by
  apply (aleph 1).ord.out.wo.wf.induction i
  intro i IH
  have A := aleph0_le_aleph 1
  have B : aleph 1 ≤ max #s 2 ^ aleph0.{u} :=
    aleph_one_le_continuum.trans (power_le_power_right (le_max_right _ _))
  have C : ℵ₀ ≤ max #s 2 ^ aleph0.{u} := A.trans B
  have J : #(⋃ j : Iio i, generateMeasurableRec s j.1) ≤ max #s 2 ^ aleph0.{u} := by
    refine (mk_iUnion_le _).trans ?_
    have D : ⨆ j : Iio i, #(generateMeasurableRec s j) ≤ _ := ciSup_le' fun ⟨j, hj⟩ => IH j hj
    apply (mul_le_mul' ((mk_subtype_le _).trans (aleph 1).mk_ord_out.le) D).trans
    rw [mul_eq_max A C]
    exact max_le B le_rfl
  rw [generateMeasurableRec]
  apply_rules [(mk_union_le _ _).trans, add_le_of_le C, mk_image_le.trans]
  · exact (le_max_left _ _).trans (self_le_power _ one_lt_aleph0.le)
  · rw [mk_singleton]
    exact one_lt_aleph0.le.trans C
  · apply mk_range_le.trans
    simp only [mk_pi, prod_const, lift_uzero, mk_denumerable, lift_aleph0]
    have := @power_le_power_right _ _ ℵ₀ J
    rwa [← power_mul, aleph0_mul_aleph0] at this

/-- `generateMeasurableRec s` generates precisely the smallest sigma-algebra containing `s`. -/
theorem generateMeasurable_eq_rec (s : Set (Set α)) :
    { t | GenerateMeasurable s t } =
        ⋃ (i : (Quotient.out (aleph 1).ord).α), generateMeasurableRec s i := by
  ext t; refine ⟨fun ht => ?_, fun ht => ?_⟩
  · inhabit ω₁
    induction' ht with u hu u _ IH f _ IH
    · exact mem_iUnion.2 ⟨default, self_subset_generateMeasurableRec s _ hu⟩
    · exact mem_iUnion.2 ⟨default, empty_mem_generateMeasurableRec s _⟩
    · rcases mem_iUnion.1 IH with ⟨i, hi⟩
      obtain ⟨j, hj⟩ := exists_gt i
      exact mem_iUnion.2 ⟨j, compl_mem_generateMeasurableRec hj hi⟩
    · have : ∀ n, ∃ i, f n ∈ generateMeasurableRec s i := fun n => by simpa using IH n
      choose I hI using this
      have : IsWellOrder (ω₁ : Type u) (· < ·) := isWellOrder_out_lt _
      refine mem_iUnion.2
        ⟨Ordinal.enum (· < ·) (Ordinal.lsub fun n => Ordinal.typein.{u} (· < ·) (I n)) ?_,
          iUnion_mem_generateMeasurableRec fun n => ⟨I n, ?_, hI n⟩⟩
      · rw [Ordinal.type_lt]
        refine Ordinal.lsub_lt_ord_lift ?_ fun i => Ordinal.typein_lt_self _
        rw [mk_denumerable, lift_aleph0, isRegular_aleph_one.cof_eq]
        exact aleph0_lt_aleph_one
      · rw [← Ordinal.typein_lt_typein (· < ·), Ordinal.typein_enum]
        apply Ordinal.lt_lsub fun n : ℕ => _
  · rcases ht with ⟨t, ⟨i, rfl⟩, hx⟩
    revert t
    apply (aleph 1).ord.out.wo.wf.induction i
    intro j H t ht
    unfold generateMeasurableRec at ht
    rcases ht with (((h | (rfl : t = ∅)) | ⟨u, ⟨-, ⟨⟨k, hk⟩, rfl⟩, hu⟩, rfl⟩) | ⟨f, rfl⟩)
    · exact .basic t h
    · exact .empty
    · exact .compl u (H k hk u hu)
    · refine .iUnion _ @fun n => ?_
      obtain ⟨-, ⟨⟨k, hk⟩, rfl⟩, hf⟩ := (f n).prop
      exact H k hk _ hf

/-- If a sigma-algebra is generated by a set of sets `s`, then the sigma-algebra has cardinality at
most `(max #s 2) ^ ℵ₀`. -/
theorem cardinal_generateMeasurable_le (s : Set (Set α)) :
    #{ t | GenerateMeasurable s t } ≤ max #s 2 ^ aleph0.{u} := by
  rw [generateMeasurable_eq_rec]
  apply (mk_iUnion_le _).trans
  rw [(aleph 1).mk_ord_out]
  refine le_trans (mul_le_mul' aleph_one_le_continuum
      (ciSup_le' fun i => cardinal_generateMeasurableRec_le s i)) ?_
  refine (mul_le_max_of_aleph0_le_left aleph0_le_continuum).trans (max_le ?_ le_rfl)
  exact power_le_power_right (le_max_right _ _)

/-- If a sigma-algebra is generated by a set of sets `s`, then the sigma
algebra has cardinality at most `(max #s 2) ^ ℵ₀`. -/
theorem cardinalMeasurableSet_le (s : Set (Set α)) :
    #{ t | @MeasurableSet α (generateFrom s) t } ≤ max #s 2 ^ aleph0.{u} :=
  cardinal_generateMeasurable_le s

/-- If a sigma-algebra is generated by a set of sets `s` with cardinality at most the continuum,
then the sigma algebra has the same cardinality bound. -/
theorem cardinal_generateMeasurable_le_continuum {s : Set (Set α)} (hs : #s ≤ 𝔠) :
    #{ t | GenerateMeasurable s t } ≤ 𝔠 :=
  (cardinal_generateMeasurable_le s).trans
    (by
      rw [← continuum_power_aleph0]
      exact mod_cast power_le_power_right (max_le hs (nat_lt_continuum 2).le))

/-- If a sigma-algebra is generated by a set of sets `s` with cardinality at most the continuum,
then the sigma algebra has the same cardinality bound. -/
theorem cardinal_measurableSet_le_continuum {s : Set (Set α)} :
    #s ≤ 𝔠 → #{ t | @MeasurableSet α (generateFrom s) t } ≤ 𝔠 :=
  cardinal_generateMeasurable_le_continuum

end MeasurableSpace
