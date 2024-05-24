/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Reid Barton
-/
import Mathlib.CategoryTheory.Limits.Types
import Mathlib.CategoryTheory.Filtered.Basic

#align_import category_theory.limits.types from "leanprover-community/mathlib"@"4aa2a2e17940311e47007f087c9df229e7f12942"

/-!
# Filtered colimits in the category of types.

We give a characterisation of the equality in filtered colimits in `Type` as a
lemma `CategoryTheory.Limits.Types.FilteredColimit.colimit_eq_iff`:
`colimit.ι F i xi = colimit.ι F j xj ↔ ∃ k (f : i ⟶ k) (g : j ⟶ k), F.map f xi = F.map g xj`.

-/

open CategoryTheory CategoryTheory.Limits

universe v u w

namespace CategoryTheory.Limits.Types.FilteredColimit

variable {J : Type v} [Category.{w} J] (F : J ⥤ Type u) [HasColimit F]

attribute [local instance] small_quot_of_hasColimit

/- For filtered colimits of types, we can give an explicit description
  of the equivalence relation generated by the relation used to form
  the colimit.  -/

/-- An alternative relation on `Σ j, F.obj j`,
which generates the same equivalence relation as we use to define the colimit in `Type` above,
but that is more convenient when working with filtered colimits.

Elements in `F.obj j` and `F.obj j'` are equivalent if there is some `k : J` to the right
where their images are equal.
-/
protected def Rel (x y : Σ j, F.obj j) : Prop :=
  ∃ (k : _) (f : x.1 ⟶ k) (g : y.1 ⟶ k), F.map f x.2 = F.map g y.2
#align category_theory.limits.types.filtered_colimit.rel CategoryTheory.Limits.Types.FilteredColimit.Rel

theorem rel_of_quot_rel (x y : Σ j, F.obj j) :
    Quot.Rel F x y → FilteredColimit.Rel.{v, u} F x y :=
  fun ⟨f, h⟩ => ⟨y.1, f, 𝟙 y.1, by rw [← h, FunctorToTypes.map_id_apply]⟩
#align category_theory.limits.types.filtered_colimit.rel_of_quot_rel CategoryTheory.Limits.Types.FilteredColimit.rel_of_quot_rel

theorem eqvGen_quot_rel_of_rel (x y : Σ j, F.obj j) :
    FilteredColimit.Rel.{v, u} F x y → EqvGen (Quot.Rel F) x y := fun ⟨k, f, g, h⟩ => by
  refine EqvGen.trans _ ⟨k, F.map f x.2⟩ _ ?_ ?_
  · exact (EqvGen.rel _ _ ⟨f, rfl⟩)
  · exact (EqvGen.symm _ _ (EqvGen.rel _ _ ⟨g, h⟩))
#align category_theory.limits.types.filtered_colimit.eqv_gen_quot_rel_of_rel CategoryTheory.Limits.Types.FilteredColimit.eqvGen_quot_rel_of_rel

--attribute [local elab_without_expected_type] nat_trans.app

/-- Recognizing filtered colimits of types. -/
noncomputable def isColimitOf (t : Cocone F) (hsurj : ∀ x : t.pt, ∃ i xi, x = t.ι.app i xi)
    (hinj :
      ∀ i j xi xj,
        t.ι.app i xi = t.ι.app j xj → ∃ (k : _) (f : i ⟶ k) (g : j ⟶ k), F.map f xi = F.map g xj) :
    IsColimit t := by
  let α : t.pt → J := fun x => (hsurj x).choose
  let f : ∀ (x : t.pt), F.obj (α x) := fun x => (hsurj x).choose_spec.choose
  have hf : ∀ (x : t.pt), x = t.ι.app _ (f x) := fun x => (hsurj x).choose_spec.choose_spec
  exact
    { desc := fun s x => s.ι.app _ (f x)
      fac := fun s j => by
        ext y
        obtain ⟨k, l, g, eq⟩ := hinj _ _ _ _ (hf (t.ι.app j y))
        have h := congr_fun (s.ι.naturality g) (f (t.ι.app j y))
        have h' := congr_fun (s.ι.naturality l) y
        dsimp at h h' ⊢
        rw [← h, ← eq, h']
      uniq := fun s m hm => by
        ext x
        dsimp
        nth_rw 1 [hf x]
        rw [← hm, types_comp_apply] }
#align category_theory.limits.types.filtered_colimit.is_colimit_of CategoryTheory.Limits.Types.FilteredColimit.isColimitOf

variable [IsFilteredOrEmpty J]

protected theorem rel_equiv : _root_.Equivalence (FilteredColimit.Rel.{v, u} F) where
  refl x := ⟨x.1, 𝟙 x.1, 𝟙 x.1, rfl⟩
  symm := fun ⟨k, f, g, h⟩ => ⟨k, g, f, h.symm⟩
  trans {x y z} := fun ⟨k, f, g, h⟩ ⟨k', f', g', h'⟩ =>
    let ⟨l, fl, gl, _⟩ := IsFilteredOrEmpty.cocone_objs k k'
    let ⟨m, n, hn⟩ := IsFilteredOrEmpty.cocone_maps (g ≫ fl) (f' ≫ gl)
    ⟨m, f ≫ fl ≫ n, g' ≫ gl ≫ n,
      calc
        F.map (f ≫ fl ≫ n) x.2 = F.map (fl ≫ n) (F.map f x.2) := by simp
        _ = F.map (fl ≫ n) (F.map g y.2) := by rw [h]
        _ = F.map ((g ≫ fl) ≫ n) y.2 := by simp
        _ = F.map ((f' ≫ gl) ≫ n) y.2 := by rw [hn]
        _ = F.map (gl ≫ n) (F.map f' y.2) := by simp
        _ = F.map (gl ≫ n) (F.map g' z.2) := by rw [h']
        _ = F.map (g' ≫ gl ≫ n) z.2 := by simp⟩
#align category_theory.limits.types.filtered_colimit.rel_equiv CategoryTheory.Limits.Types.FilteredColimit.rel_equiv

protected theorem rel_eq_eqvGen_quot_rel :
    FilteredColimit.Rel.{v, u} F = EqvGen (Quot.Rel F) := by
  ext ⟨j, x⟩ ⟨j', y⟩
  constructor
  · apply eqvGen_quot_rel_of_rel
  · rw [← (FilteredColimit.rel_equiv F).eqvGen_iff]
    exact EqvGen.mono (rel_of_quot_rel F)
#align category_theory.limits.types.filtered_colimit.rel_eq_eqv_gen_quot_rel CategoryTheory.Limits.Types.FilteredColimit.rel_eq_eqvGen_quot_rel

theorem colimit_eq_iff_aux {i j : J} {xi : F.obj i} {xj : F.obj j} :
    (colimitCocone F).ι.app i xi = (colimitCocone F).ι.app j xj ↔
      FilteredColimit.Rel.{v, u} F ⟨i, xi⟩ ⟨j, xj⟩ := by
  dsimp
  rw [← (equivShrink _).symm.injective.eq_iff, Equiv.symm_apply_apply, Equiv.symm_apply_apply,
    Quot.eq, FilteredColimit.rel_eq_eqvGen_quot_rel]
#align category_theory.limits.types.filtered_colimit.colimit_eq_iff_aux CategoryTheory.Limits.Types.FilteredColimit.colimit_eq_iff_aux

theorem isColimit_eq_iff {t : Cocone F} (ht : IsColimit t) {i j : J} {xi : F.obj i} {xj : F.obj j} :
    t.ι.app i xi = t.ι.app j xj ↔ ∃ (k : _) (f : i ⟶ k) (g : j ⟶ k), F.map f xi = F.map g xj := by
  refine Iff.trans ?_ (colimit_eq_iff_aux F)
  rw [← (IsColimit.coconePointUniqueUpToIso ht (colimitCoconeIsColimit F)).toEquiv.injective.eq_iff]
  convert Iff.rfl
  · exact (congrFun
      (IsColimit.comp_coconePointUniqueUpToIso_hom ht (colimitCoconeIsColimit F) _) xi).symm
  · exact (congrFun
      (IsColimit.comp_coconePointUniqueUpToIso_hom ht (colimitCoconeIsColimit F) _) xj).symm
#align category_theory.limits.types.filtered_colimit.is_colimit_eq_iff CategoryTheory.Limits.Types.FilteredColimit.isColimit_eq_iff

theorem colimit_eq_iff {i j : J} {xi : F.obj i} {xj : F.obj j} :
    colimit.ι F i xi = colimit.ι F j xj ↔
      ∃ (k : _) (f : i ⟶ k) (g : j ⟶ k), F.map f xi = F.map g xj :=
  isColimit_eq_iff _ (colimit.isColimit F)
#align category_theory.limits.types.filtered_colimit.colimit_eq_iff CategoryTheory.Limits.Types.FilteredColimit.colimit_eq_iff

end CategoryTheory.Limits.Types.FilteredColimit
