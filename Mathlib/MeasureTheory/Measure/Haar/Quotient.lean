/-
Copyright (c) 2022 Alex Kontorovich and Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich, Heather Macbeth
-/
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.Algebra.Group.Opposite
import Mathlib.MeasureTheory.Constructions.Polish

#align_import measure_theory.measure.haar.quotient from "leanprover-community/mathlib"@"fd5edc43dc4f10b85abfe544b88f82cf13c5f844"

/-!
# Haar quotient measure

In this file, we consider properties of fundamental domains and measures for the action of a
subgroup of a group `G` on `G` itself.

## Main results

* `MeasureTheory.IsFundamentalDomain.smulInvariantMeasure_map `: given a subgroup `Γ` of a
  topological group `G`, the pushforward to the coset space `G ⧸ Γ` of the restriction of a both
  left- and right-invariant measure on `G` to a fundamental domain `𝓕` is a `G`-invariant measure
  on `G ⧸ Γ`.

* `MeasureTheory.IsFundamentalDomain.isMulLeftInvariant_map `: given a normal subgroup `Γ` of
  a topological group `G`, the pushforward to the quotient group `G ⧸ Γ` of the restriction of
  a both left- and right-invariant measure on `G` to a fundamental domain `𝓕` is a left-invariant
  measure on `G ⧸ Γ`.

Note that a group `G` with Haar measure that is both left and right invariant is called
**unimodular**.
-/

open Set MeasureTheory TopologicalSpace MeasureTheory.Measure

open scoped Pointwise NNReal

section SigmaFiniteSmul

--move to `Mathlib.Data.Set.Lattice`

theorem Set.iUnion_equiv {α ι ι' : Type _} (f : ι → Set α) (g : Equiv ι' ι) :
    (⋃ i, (f ∘ g) i) = ⋃ i, f i := Equiv.iSup_congr g (congrFun rfl)


-- move
theorem Set.iUnion_inter_iUnion {α ι ι' : Type _} (A : ι → Set α) (B : ι' → Set α) :
    (⋃ (i : ι) (j : ι'), A i ∩ B j) = (⋃ (i : ι), A i) ∩ (⋃ (j : ι'), B j) := by
  rw [Set.iUnion_inter]
  apply Set.iUnion_congr
  intro i
  rw [Set.inter_iUnion]

--- move same place
theorem Set.iUnion_prod_dom {α ι ι' : Type _} (f : ι × ι' → Set α) :
    (⋃ (x : ι × ι'), f x) = (⋃ (i : ι) (j : ι'), f (i, j)) := iSup_prod (f := f)

theorem MeasureTheory.SigmaFinite.add {α : Type u_1} {m0 : MeasurableSpace α}
    {μ ν : MeasureTheory.Measure α} (hμ : MeasureTheory.SigmaFinite μ)
    (hν : MeasureTheory.SigmaFinite ν) : MeasureTheory.SigmaFinite (μ + ν) := by
  sorry --- exists already

end SigmaFiniteSmul

section

variable {G : Type _} [Group G] [MeasurableSpace G] [TopologicalSpace G] [TopologicalGroup G]
  [BorelSpace G] {Γ : Subgroup G} [PolishSpace G] [T2Space (G ⧸ Γ)]
  [SecondCountableTopology (G ⧸ Γ)]

--- TODO: move to `measure_theory.constructions.polish`
instance CosetSpace.borelSpace {G : Type _} [TopologicalSpace G] [PolishSpace G]
    [Group G] [MeasurableSpace G] [BorelSpace G] {N : Subgroup G} [T2Space (G ⧸ N)]
    [SecondCountableTopology (G ⧸ N)] : BorelSpace (G ⧸ N) := Quotient.borelSpace

/-- Measurability of the action of the topological group `G` on the left-coset space `G / Γ`. -/
--@[to_additive "Measurability of the action of the additive topological group `G` on the left-coset
--  space `G / Γ`."]
instance QuotientGroup.measurableSMul [PolishSpace G] [T2Space (G ⧸ Γ)]
    [SecondCountableTopology (G ⧸ Γ)] : MeasurableSMul G (G ⧸ Γ) where
  measurable_const_smul g := (continuous_const_smul g).measurable
  measurable_smul_const x := (QuotientGroup.continuous_smul₁ x).measurable
#align quotient_group.has_measurable_smul QuotientGroup.measurableSMul
--#align quotient_add_group.has_measurable_vadd QuotientAddGroup.measurableVAdd

end

section smulInvariantMeasure

variable {G : Type _} [Group G] [MeasureSpace G] [TopologicalSpace G] [TopologicalGroup G]
  [BorelSpace G] {Γ : Subgroup G} [PolishSpace G] [T2Space (G ⧸ Γ)]
  [SecondCountableTopology (G ⧸ Γ)]

--variable {𝓕 : Set G} (h𝓕 : IsFundamentalDomain (Subgroup.opposite Γ) 𝓕 μ)

variable {μ : Measure (G ⧸ Γ)}

local notation "π" => @QuotientGroup.mk G _ Γ

-- set_option linter.unusedVariables false in
-- class QuotientVolumeEqVolumePreimage' [MeasureSpace (G ⧸ Γ)] : Prop where
--   projection_respects_measure : ∀ (t : Set G)
--   (fund_dom_t : IsFundamentalDomain (Subgroup.opposite Γ) t)
--     (meas_t : MeasurableSet t) (U : Set (G ⧸ Γ)) (meas_U : MeasurableSet U),
--     volume U = volume (π ⁻¹' U ∩ t)


variable [Countable Γ] --[MeasureSpace G] -- [MeasureSpace (G ⧸ Γ)]
  [QuotientVolumeEqVolumePreimage (Subgroup.opposite Γ) G μ]
--[BorelSpace (G ⧸ Γ)]


-- more beautiful theorem: if you have a measure speace downstairs and the downstairs one is smul invariant
-- then fund dom independent

/-- The pushforward to the coset space `G ⧸ Γ` of the restriction of a both left- and right-
  invariant measure on `G` to is a `G`-invariant measure on `G ⧸ Γ`. -/
-- @[to_additive "The pushforward to the coset space `G ⧸ Γ` of the restriction of a both left- and
--   right-invariant measure on an additive topological group `G` to a fundamental domain `𝓕` is a
--   `G`-invariant measure on `G ⧸ Γ`."]
instance MeasureTheory.QuotientVolumeEqVolumePreimage.smulInvariantMeasure_quotient
    [IsMulLeftInvariant (volume : Measure G)] [IsMulRightInvariant (volume : Measure G)]
    [hasFun : HasFundamentalDomain (Subgroup.opposite Γ) G] :
    SMulInvariantMeasure G (G ⧸ Γ) μ where
  measure_preimage_smul g A hA := by
    have meas_π : Measurable π := continuous_quotient_mk'.measurable
    have meas_πA : MeasurableSet (π ⁻¹' A) := measurableSet_preimage meas_π hA
    obtain ⟨𝓕, h𝓕, meas_𝓕⟩ := hasFun.has_fundamental_domain_characterization
    have meas_g𝓕 : MeasurableSet (g • 𝓕)
    · rw [← preimage_smul_inv]
      exact (@measurable_const_smul G G _ _ _ _ (g⁻¹)) meas_𝓕
    have h𝓕_translate_fundom : IsFundamentalDomain (Subgroup.opposite Γ) (g • 𝓕) volume :=
      h𝓕.smul_of_comm g
    rw [QuotientVolumeEqVolumePreimage.projection_respects_measure 𝓕 h𝓕 meas_𝓕 _
      (meas_π (measurableSet_preimage (measurable_const_smul g) hA)),
      QuotientVolumeEqVolumePreimage.projection_respects_measure _ h𝓕_translate_fundom meas_g𝓕 _
      hA]
    change volume ((π ⁻¹' _) ∩ _) = _
    set π_preA := π ⁻¹' A
    have : π ⁻¹' ((fun x : G ⧸ Γ => g • x) ⁻¹' A) = (g * ·) ⁻¹' π_preA := by ext1; simp
    rw [this]
    have : volume ((g * ·) ⁻¹' π_preA ∩ 𝓕) = volume (π_preA ∩ (g⁻¹ * ·) ⁻¹' 𝓕)
    · trans volume ((g * ·) ⁻¹' (π_preA ∩ (g⁻¹ * ·) ⁻¹' 𝓕))
      · rw [preimage_inter]
        congr 2
        simp [Set.preimage]
      rw [measure_preimage_mul]
    rw [this, ← preimage_smul_inv]; rfl

/-- Given a subgroup `Γ` of a topological group `G` with Haar measure `volume`, with a measure 'μ'
  on the quotient `G ⧸ Γ` satisfying `QuotientVolumeEqVolumePreimage`, the restriction of `volume`
  to a fundamental domain is measure-preserving with respect to `μ`. -/
theorem measurePreserving_quotientGroup_mk_of_quotientVolumeEqVolumePreimage
    [IsMulLeftInvariant (volume : Measure G)] [IsMulRightInvariant (volume : Measure G)]
    (𝓕 : Set G) (h𝓕 : IsFundamentalDomain (Subgroup.opposite Γ) 𝓕)
    (meas_𝓕 : MeasurableSet 𝓕) (μ : Measure (G ⧸ Γ))
    [QuotientVolumeEqVolumePreimage (Subgroup.opposite Γ) G μ] :
    MeasurePreserving (@QuotientGroup.mk G _ Γ) (volume.restrict 𝓕) μ := by
  apply measurePreserving_quotient_mk_of_quotientVolumeEqVolumePreimage
  · assumption
  · assumption


---- the quotient measure is finite, assuming the covolume is finite
theorem MeasureTheory.QuotientVolumeEqVolumePreimage.Finite_quotient
    [IsMulRightInvariant (volume : Measure G)]
    [hasFun : HasFundamentalDomain (Subgroup.opposite Γ) G]
    (h : hasFun.covolume ≠ ⊤) :
    IsFiniteMeasure μ := by
  obtain ⟨𝓕, h𝓕, meas_𝓕⟩ := hasFun.has_fundamental_domain_characterization
  rw [@QuotientVolumeEqVolumePreimage.eq_map_restrict (s := 𝓕) (G := Subgroup.opposite Γ) _
    _ _ _ _ _ _ meas_𝓕 h𝓕 μ _]
  have : Fact (volume 𝓕 < ⊤) := by
    apply Fact.mk
    convert Ne.lt_top h
    rw [hasFun.covolume_eq_volume]
    exact h𝓕
  exact inferInstance

end smulInvariantMeasure

section mulInvariantMeasure


variable {G : Type _} [Group G] [MeasureSpace G] [TopologicalSpace G] [TopologicalGroup G]
  [BorelSpace G] {Γ : Subgroup G} [PolishSpace G] [T2Space (G ⧸ Γ)]
  [SecondCountableTopology (G ⧸ Γ)] {μ : Measure (G ⧸ Γ)}
  [Countable Γ] [QuotientVolumeEqVolumePreimage (Subgroup.opposite Γ) G μ]

/-- Assuming `Γ` is a normal subgroup of a topological group `G`, the pushforward to the quotient
  group `G ⧸ Γ` of the restriction of a both left- and right-invariant measure on `G` to a
  fundamental domain `𝓕` is a left-invariant measure on `G ⧸ Γ`. -/
-- @[to_additive "Assuming `Γ` is a normal subgroup of an additive topological group `G`, the
--   pushforward to the quotient group `G ⧸ Γ` of the restriction of a both left- and right-invariant
--   measure on `G` to a fundamental domain `𝓕` is a left-invariant measure on `G ⧸ Γ`."]
instance MeasureTheory.QuotientVolumeEqVolumePreimage.MulInvariantMeasure_quotient
    [Subgroup.Normal Γ] [IsMulLeftInvariant (volume : Measure G)]
    [IsMulRightInvariant (volume : Measure G)]
    [hasFun : HasFundamentalDomain (Subgroup.opposite Γ) G]  :
    μ.IsMulLeftInvariant where
  map_mul_left_eq_self x := by
    apply Measure.ext
    intro A hA
    obtain ⟨x₁, h⟩ := @Quotient.exists_rep _ (QuotientGroup.leftRel Γ) x
    --haveI := h𝓕.smulInvariantMeasure_map
    convert measure_preimage_smul x₁ μ A using 1
    rw [← h, Measure.map_apply]
    · rfl
    · exact measurable_const_mul _
    · exact hA

end mulInvariantMeasure

section HaarIsQuotientVolumeEqVolumePreimage

variable {G : Type _} [Group G] [MeasureSpace G] [TopologicalSpace G] [TopologicalGroup G]
  [BorelSpace G] {Γ : Subgroup G} [PolishSpace G] [T2Space (G ⧸ Γ)]
  [SecondCountableTopology (G ⧸ Γ)] [Countable Γ] [Subgroup.Normal Γ]
  [IsMulLeftInvariant (volume : Measure G)] [IsMulRightInvariant (volume : Measure G)]
  {μ : Measure (G ⧸ Γ)} [IsHaarMeasure μ] [SigmaFinite μ]
  -- Note: couldn't get uniqueness without sigma finiteness

/-- If a measure `μ` is `IsHaarMeasure` and satisfies the right scaling condition, then it
  satisfies `QuotientVolumeEqVolumePreimage`. -/
theorem MeasureTheory.HaarIsQuotientVolumeEqVolumePreimage
    [hasFun : HasFundamentalDomain (Subgroup.opposite Γ) G]
    (h : hasFun.covolume = μ univ)
    (finiteCovol : hasFun.covolume ≠ ⊤) :
    QuotientVolumeEqVolumePreimage (Subgroup.opposite Γ) G μ where
      projection_respects_measure := by
        intro 𝓕 h𝓕 meas_𝓕 U meas_U
        let π := @QuotientGroup.mk G _ Γ
        let μ' := Measure.map π (volume.restrict 𝓕)
        have QVEVPμ' : QuotientVolumeEqVolumePreimage (Subgroup.opposite Γ) G μ' :=
            quotientVolumeEqVolumePreimage_map_restrict (G := (Subgroup.opposite Γ)) G 𝓕 meas_𝓕 h𝓕
        have Fin_μ' : IsFiniteMeasure μ' :=
          QuotientVolumeEqVolumePreimage.Finite_quotient finiteCovol
        have covol_𝓕 : hasFun.covolume = volume 𝓕
        · rw [hasFun.covolume_eq_volume 𝓕 h𝓕]
        rw [covol_𝓕] at finiteCovol h
        by_cases meas_𝓕_ne_zero : volume 𝓕 = 0
        · trans (0 : ENNReal)
          · rw [← le_zero_iff]
            calc μ U ≤ μ univ := measure_mono (Set.subset_univ _)
                _   = _ := h.symm
                _   = 0 := meas_𝓕_ne_zero
          · symm
            rw [← le_zero_iff]
            calc _ ≤ volume 𝓕 := measure_mono (Set.inter_subset_right _ _)
                _   = 0 := meas_𝓕_ne_zero
        suffices : μ =  μ'
        · rw [this]
          rw [Measure.map_apply]
          · rw [Measure.restrict_apply]
            · rfl
            · exact @measurable_quotient_mk' _ _ (MulAction.orbitRel (Subgroup.opposite Γ) G) U
                meas_U
          · exact @measurable_quotient_mk' _ _ (MulAction.orbitRel (Subgroup.opposite Γ) G)
          · exact meas_U
        · have : μ'.IsMulLeftInvariant :=
            MeasureTheory.QuotientVolumeEqVolumePreimage.MulInvariantMeasure_quotient
          rw [measure_eq_div_smul (μ := μ') (ν := μ) (s := univ), ← h]
          simp only
          rw [Measure.map_apply, Measure.restrict_apply, preimage_univ, Set.univ_inter]
          rw [ENNReal.div_self, one_smul]
          · exact meas_𝓕_ne_zero
          · exact finiteCovol
          · rw [preimage_univ]
            exact MeasurableSet.univ
          · exact QuotientGroup.measurable_coe
          · exact MeasurableSet.univ
          · exact MeasurableSet.univ
          · rw [←h]
            exact meas_𝓕_ne_zero
          · rw [←h]
            exact finiteCovol

end HaarIsQuotientVolumeEqVolumePreimage


section QuotientIsHaar

variable {G : Type _} [Group G] [MeasureSpace G] [TopologicalSpace G] [TopologicalGroup G]
  [BorelSpace G] {Γ : Subgroup G} [PolishSpace G] [i : T2Space (G ⧸ Γ)]
  [ii : SecondCountableTopology (G ⧸ Γ)] {μ : Measure (G ⧸ Γ)}
  [Countable Γ] [QuotientVolumeEqVolumePreimage (Subgroup.opposite Γ) G μ]

variable [T2Space (G ⧸ Γ)] [SecondCountableTopology (G ⧸ Γ)] (K : PositiveCompacts (G ⧸ Γ))

/-- Given a normal cofinite subgroup `Γ` of a topological group `G` with Haar measure `μ`, which is
  also right-invariant, and a measure `μ` on `G ⧸ Γ` which is compatible under the quotient map
  with the volume on `G`, that measure `μ` is a multiple of Haar measure on `G ⧸ Γ`. -/
theorem MeasureTheory.QuotientVolumeEqVolumePreimage.quotient_is_haar [Subgroup.Normal Γ]
    [MeasureTheory.Measure.IsHaarMeasure (volume : Measure G)]
    [hasFun : HasFundamentalDomain (Subgroup.opposite Γ) G] [IsMulRightInvariant (volume : Measure G)]
    (h : hasFun.covolume < ⊤) :
    μ = μ K • MeasureTheory.Measure.haarMeasure K := by
  have : IsFiniteMeasure μ := QuotientVolumeEqVolumePreimage.Finite_quotient h.ne
  rw [Measure.haarMeasure_unique μ K, Measure.smul_apply, Measure.haarMeasure_self]
  simp


--- 7/21/23
-- Need a lemma about our magic typeclass:
-- Lemma: behavior under scaling


/-- Any map on the zero measures is `MeasurePreserving` -/
theorem MeasurePreserving.zero {f : X → Y} [MeasurableSpace X] [MeasurableSpace Y]
    (hf : Measurable f) : MeasurePreserving f 0 0 where
      measurable := hf
      map_eq := Measure.map_zero f


--- Keeping or not?
/-- Given a normal subgroup `Γ` of a topological group `G` with Haar measure `μ`, which is also
  right-invariant, and a finite volume fundamental domain `𝓕`, the quotient map to `G ⧸ Γ` is
  measure-preserving between appropriate multiples of Haar measure on `G` and `G ⧸ Γ`. -/
theorem MeasurePreserving_QuotientGroup.foo [Subgroup.Normal Γ]
    [MeasureTheory.Measure.IsHaarMeasure (volume : Measure G)]

    --[T2Space G] [LocallyCompactSpace G] [ProperlyDiscontinuousSMul Γ G]
    -- needed to add for `MeasureTheory.Measure.sigmaFinite_haarMeasure`
    -- Instead:
    [T2Space (G ⧸ Γ)]
  -- haveI : T2Space (G ⧸ Γ) := by
  --   --exact @t2Space_of_properlyDiscontinuousSMul_of_t2Space (Γ := Γ) (T := G) _ _ _ _ _ _ _
  --   sorry


    [BorelSpace (G ⧸ Γ)] -- needed for `MeasureTheory.Measure.sigmaFinite_haarMeasure`


    [IsMulRightInvariant (volume : Measure G)] (𝓕 : Set G)
    (h𝓕 : IsFundamentalDomain (Subgroup.opposite Γ) 𝓕)
    (meas_𝓕 : MeasurableSet 𝓕) (h𝓕_finite : volume 𝓕 ≠ ⊤) :
    MeasurePreserving (QuotientGroup.mk' Γ) (volume.restrict 𝓕)
      ((volume ((QuotientGroup.mk' Γ ⁻¹' (K : Set (G ⧸ Γ))) ∩ 𝓕)) •
      MeasureTheory.Measure.haarMeasure K) := by
  set c := volume ((QuotientGroup.mk' Γ ⁻¹' (K : Set (G ⧸ Γ))) ∩ 𝓕)
  have vol_int_nonzero : volume (interior (QuotientGroup.mk' Γ ⁻¹' (K : Set (G ⧸ Γ)))) ≠ 0
  · have : (QuotientGroup.mk' Γ ⁻¹' (interior (K : Set (G ⧸ Γ)))) ⊆
      (interior (QuotientGroup.mk' Γ ⁻¹' (K : Set (G ⧸ Γ)))) :=
      preimage_interior_subset_interior_preimage continuous_coinduced_rng
    have : Set.Nonempty (interior (QuotientGroup.mk' Γ ⁻¹' (K : Set (G ⧸ Γ))))
    · apply Set.Nonempty.mono this
      apply Set.Nonempty.preimage' K.interior_nonempty
      simp
    refine @MeasureTheory.Measure.IsOpenPosMeasure.open_pos G _ _ volume _ _ ?_ this
    simp
  have : volume (QuotientGroup.mk' Γ ⁻¹' (K : Set (G ⧸ Γ))) ≠ 0
  · intro h_v
    have : interior (QuotientGroup.mk' Γ ⁻¹' (K : Set (G ⧸ Γ))) ⊆
        QuotientGroup.mk' Γ ⁻¹' (K : Set (G ⧸ Γ)) :=
      interior_subset
    exact vol_int_nonzero (@MeasureTheory.measure_mono_null _ _ _ _ _ this h_v)
  have c_nonzero : c ≠ 0
  · contrapose! this
    apply h𝓕.measure_zero_of_invariant
    · intro g
      simp only [QuotientGroup.coe_mk']
      sorry -- ALEX HOMEWORK ???
    · exact this
  have c_ne_top : c ≠ ⊤
  · contrapose! h𝓕_finite
    have : volume (↑(QuotientGroup.mk' Γ) ⁻¹' ↑K ∩ 𝓕) ≤ volume 𝓕 :=
      measure_mono (Set.inter_subset_right _ _)
    rw [h𝓕_finite] at this
    exact top_unique this
  set μ := c • haarMeasure K --Measure.map (QuotientGroup.mk' Γ) (volume.restrict 𝓕)
  haveI : IsHaarMeasure μ := IsHaarMeasure.smul _ c_nonzero c_ne_top
  haveI : SigmaFinite μ := by
    let c' := ENNReal.toNNReal c
    have c'_eq_c : c = c' := (ENNReal.coe_toNNReal c_ne_top).symm
    have := @MeasureTheory.Measure.sigmaFinite_haarMeasure (K₀ := K) _ _ _ _ _ _ _
    convert @MeasureTheory.SMul.sigmaFinite (c := c') (μ := haarMeasure K) this
    ext U meas_U
    simp only [nnreal_smul_coe_apply]
    congr
  haveI hasDom : HasFundamentalDomain (Subgroup.opposite Γ) G := {
    has_fundamental_domain_characterization := ⟨𝓕, h𝓕, meas_𝓕⟩
  }
  haveI : QuotientVolumeEqVolumePreimage (Subgroup.opposite Γ) G μ := by
    apply MeasureTheory.HaarIsQuotientVolumeEqVolumePreimage
    · rw [hasDom.covolume_eq_volume 𝓕 h𝓕]
      norm_cast
      simp only [QuotientGroup.coe_mk', Pi.smul_apply, smul_eq_mul]
      sorry -- ???
    · convert h𝓕_finite
      rw [hasDom.covolume_eq_volume 𝓕 h𝓕]
  apply measurePreserving_quotientGroup_mk_of_quotientVolumeEqVolumePreimage
  · exact h𝓕
  · exact meas_𝓕

end QuotientIsHaar
