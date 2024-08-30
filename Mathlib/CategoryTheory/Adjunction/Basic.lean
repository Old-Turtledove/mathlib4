/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Johan Commelin, Bhavik Mehta
-/
import Mathlib.CategoryTheory.Equivalence

/-!
# Adjunctions between functors

`F ⊣ G` represents the data of an adjunction between two functors
`F : C ⥤ D` and `G : D ⥤ C`. `F` is the left adjoint and `G` is the right adjoint.

We provide various useful constructors:
* `mkOfHomEquiv`
* `mkOfUnitCounit`
* `leftAdjointOfEquiv` / `rightAdjointOfEquiv`
  construct a left/right adjoint of a given functor given the action on objects and
  the relevant equivalence of morphism spaces.
* `adjunctionOfEquivLeft` / `adjunctionOfEquivRight` witness that these constructions
  give adjunctions.

There are also typeclasses `IsLeftAdjoint` / `IsRightAdjoint`, which asserts the
existence of a adjoint functor. Given `[F.IsLeftAdjoint]`, a chosen right
adjoint can be obtained as `F.rightAdjoint`.

`Adjunction.comp` composes adjunctions.

`toEquivalence` upgrades an adjunction to an equivalence,
given witnesses that the unit and counit are pointwise isomorphisms.
Conversely `Equivalence.toAdjunction` recovers the underlying adjunction from an equivalence.
-/


namespace CategoryTheory

open Category

-- declare the `v`'s first; see `CategoryTheory.Category` for an explanation
universe v₁ v₂ v₃ u₁ u₂ u₃

-- Porting Note: `elab_without_expected_type` cannot be a local attribute
-- attribute [local elab_without_expected_type] whiskerLeft whiskerRight

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- `F ⊣ G` represents the data of an adjunction between two functors
`F : C ⥤ D` and `G : D ⥤ C`. `F` is the left adjoint and `G` is the right adjoint.

To construct an `adjunction` between two functors, it's often easier to instead use the
constructors `mkOfHomEquiv` or `mkOfUnitCounit`. To construct a left adjoint,
there are also constructors `leftAdjointOfEquiv` and `adjunctionOfEquivLeft` (as
well as their duals) which can be simpler in practice.

Uniqueness of adjoints is shown in `CategoryTheory.Adjunction.Unique`.

See <https://stacks.math.columbia.edu/tag/0037>.
-/
structure Adjunction (F : C ⥤ D) (G : D ⥤ C) where
  /-- The equivalence between `Hom (F X) Y` and `Hom X (G Y)` coming from an adjunction -/
  unit : 𝟭 C ⟶ F.comp G
  /-- The counit of an adjunction -/
  counit : G.comp F ⟶ 𝟭 D
  /-- Equality of the composition of the unit, associator, and counit with the identity
  `F ⟶ (F G) F ⟶ F (G F) ⟶ F = NatTrans.id F` -/
  left_triangle_components (X : C) :
      F.map (unit.app X) ≫ counit.app (F.obj X) = 𝟙 (F.obj X) := by aesop_cat
  /-- Equality of the composition of the unit, associator, and counit with the identity
  `G ⟶ G (F G) ⟶ (F G) F ⟶ G = NatTrans.id G` -/
  right_triangle_components (Y : D) :
      unit.app (G.obj Y) ≫ G.map (counit.app Y) = 𝟙 (G.obj Y) := by aesop_cat

/-- The notation `F ⊣ G` stands for `Adjunction F G` representing that `F` is left adjoint to `G` -/
infixl:15 " ⊣ " => Adjunction

namespace Functor

/-- A class asserting the existence of a right adjoint. -/
class IsLeftAdjoint (left : C ⥤ D) : Prop where
  exists_rightAdjoint : ∃ (right : D ⥤ C), Nonempty (left ⊣ right)

/-- A class asserting the existence of a left adjoint. -/
class IsRightAdjoint (right : D ⥤ C) : Prop where
  exists_leftAdjoint : ∃ (left : C ⥤ D), Nonempty (left ⊣ right)

/-- A chosen left adjoint to a functor that is a right adjoint. -/
noncomputable def leftAdjoint (R : D ⥤ C) [IsRightAdjoint R] : C ⥤ D :=
  (IsRightAdjoint.exists_leftAdjoint (right := R)).choose

/-- A chosen right adjoint to a functor that is a left adjoint. -/
noncomputable def rightAdjoint (L : C ⥤ D) [IsLeftAdjoint L] : D ⥤ C :=
  (IsLeftAdjoint.exists_rightAdjoint (left := L)).choose

end Functor

/-- The adjunction associated to a functor known to be a left adjoint. -/
noncomputable def Adjunction.ofIsLeftAdjoint (left : C ⥤ D) [left.IsLeftAdjoint] :
    left ⊣ left.rightAdjoint :=
  Functor.IsLeftAdjoint.exists_rightAdjoint.choose_spec.some

/-- The adjunction associated to a functor known to be a right adjoint. -/
noncomputable def Adjunction.ofIsRightAdjoint (right : C ⥤ D) [right.IsRightAdjoint] :
    right.leftAdjoint ⊣ right :=
  Functor.IsRightAdjoint.exists_leftAdjoint.choose_spec.some

namespace Adjunction

attribute [reassoc (attr := simp)] left_triangle_components right_triangle_components

/-- The hom set equivalence associated to an adjunction. -/
@[simps]
def homEquiv {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) (X : C) (Y : D) :
    (F.obj X ⟶ Y) ≃ (X ⟶ G.obj Y) where
  toFun := fun f => adj.unit.app X ≫ G.map f
  invFun := fun g => F.map g ≫ adj.counit.app Y
  left_inv := fun f => by
    dsimp
    rw [F.map_comp, assoc, ← Functor.comp_map, adj.counit.naturality, ← assoc]
    simp
  right_inv := fun g => by
    simp [← assoc, ← Functor.comp_map, ← adj.unit.naturality, assoc]

alias homEquiv_unit := homEquiv_apply
alias homEquiv_counit := homEquiv_symm_apply
attribute [simp] homEquiv_unit homEquiv_counit

section

variable {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)

lemma isLeftAdjoint (adj : F ⊣ G) : F.IsLeftAdjoint := ⟨_, ⟨adj⟩⟩

lemma isRightAdjoint (adj : F ⊣ G) : G.IsRightAdjoint := ⟨_, ⟨adj⟩⟩

instance (R : D ⥤ C) [R.IsRightAdjoint] : R.leftAdjoint.IsLeftAdjoint :=
  (ofIsRightAdjoint R).isLeftAdjoint

instance (L : C ⥤ D) [L.IsLeftAdjoint] : L.rightAdjoint.IsRightAdjoint :=
  (ofIsLeftAdjoint L).isRightAdjoint

variable {X' X : C} {Y Y' : D}

theorem homEquiv_id (X : C) : adj.homEquiv X _ (𝟙 _) = adj.unit.app X := by simp

theorem homEquiv_symm_id (X : D) : (adj.homEquiv _ X).symm (𝟙 _) = adj.counit.app X := by simp

theorem homEquiv_naturality_left_symm (f : X' ⟶ X) (g : X ⟶ G.obj Y) :
    (adj.homEquiv X' Y).symm (f ≫ g) = F.map f ≫ (adj.homEquiv X Y).symm g := by
  simp

theorem homEquiv_naturality_left (f : X' ⟶ X) (g : F.obj X ⟶ Y) :
    (adj.homEquiv X' Y) (F.map f ≫ g) = f ≫ (adj.homEquiv X Y) g := by
  rw [← Equiv.eq_symm_apply]
  simp only [Equiv.symm_apply_apply, eq_self_iff_true, homEquiv_naturality_left_symm]

theorem homEquiv_naturality_right (f : F.obj X ⟶ Y) (g : Y ⟶ Y') :
    (adj.homEquiv X Y') (f ≫ g) = (adj.homEquiv X Y) f ≫ G.map g := by
  simp

theorem homEquiv_naturality_right_symm (f : X ⟶ G.obj Y) (g : Y ⟶ Y') :
    (adj.homEquiv X Y').symm (f ≫ G.map g) = (adj.homEquiv X Y).symm f ≫ g := by
  rw [Equiv.symm_apply_eq]
  simp only [homEquiv_naturality_right, eq_self_iff_true, Equiv.apply_symm_apply]

@[reassoc]
theorem homEquiv_naturality_left_square (f : X' ⟶ X) (g : F.obj X ⟶ Y')
    (h : F.obj X' ⟶ Y) (k : Y ⟶ Y') (w : F.map f ≫ g = h ≫ k) :
    f ≫ (adj.homEquiv X Y') g = (adj.homEquiv X' Y) h ≫ G.map k := by
  rw [← homEquiv_naturality_left, ← homEquiv_naturality_right, w]

@[reassoc]
theorem homEquiv_naturality_right_square (f : X' ⟶ X) (g : X ⟶ G.obj Y')
    (h : X' ⟶ G.obj Y) (k : Y ⟶ Y') (w : f ≫ g = h ≫ G.map k) :
    F.map f ≫ (adj.homEquiv X Y').symm g = (adj.homEquiv X' Y).symm h ≫ k := by
  rw [← homEquiv_naturality_left_symm, ← homEquiv_naturality_right_symm, w]

theorem homEquiv_naturality_left_square_iff (f : X' ⟶ X) (g : F.obj X ⟶ Y')
    (h : F.obj X' ⟶ Y) (k : Y ⟶ Y') :
    (f ≫ (adj.homEquiv X Y') g = (adj.homEquiv X' Y) h ≫ G.map k) ↔
      (F.map f ≫ g = h ≫ k) :=
  ⟨fun w ↦ by simpa only [Equiv.symm_apply_apply]
      using homEquiv_naturality_right_square adj _ _ _ _ w,
    homEquiv_naturality_left_square adj f g h k⟩

theorem homEquiv_naturality_right_square_iff (f : X' ⟶ X) (g : X ⟶ G.obj Y')
    (h : X' ⟶ G.obj Y) (k : Y ⟶ Y') :
    (F.map f ≫ (adj.homEquiv X Y').symm g = (adj.homEquiv X' Y).symm h ≫ k) ↔
      (f ≫ g = h ≫ G.map k) :=
  ⟨fun w ↦ by simpa only [Equiv.apply_symm_apply]
      using homEquiv_naturality_left_square adj _ _ _ _ w,
    homEquiv_naturality_right_square adj f g h k⟩

@[simp]
theorem left_triangle : whiskerRight adj.unit F ≫ whiskerLeft F adj.counit = 𝟙 _ := by
  ext; simp

@[simp]
theorem right_triangle : whiskerLeft G adj.unit ≫ whiskerRight adj.counit G = 𝟙 _ := by
  ext; simp

@[reassoc (attr := simp)]
theorem counit_naturality {X Y : D} (f : X ⟶ Y) :
    F.map (G.map f) ≫ adj.counit.app Y = adj.counit.app X ≫ f :=
  adj.counit.naturality f

@[reassoc (attr := simp)]
theorem unit_naturality {X Y : C} (f : X ⟶ Y) :
    adj.unit.app X ≫ G.map (F.map f) = f ≫ adj.unit.app Y :=
  (adj.unit.naturality f).symm

theorem homEquiv_apply_eq {A : C} {B : D} (f : F.obj A ⟶ B) (g : A ⟶ G.obj B) :
    adj.homEquiv A B f = g ↔ f = (adj.homEquiv A B).symm g :=
  ⟨fun h => by
    cases h
    simp, fun h => by
    cases h
    simp⟩

theorem eq_homEquiv_apply {A : C} {B : D} (f : F.obj A ⟶ B) (g : A ⟶ G.obj B) :
    g = adj.homEquiv A B f ↔ (adj.homEquiv A B).symm g = f :=
  ⟨fun h => by
    cases h
    simp, fun h => by
    cases h
    simp⟩

end

end Adjunction

namespace Adjunction

/--
This is an auxiliary data structure useful for constructing adjunctions.
See `Adjunction.mk'`. This structure won't typically be used anywhere else.
-/
structure CoreHomEquivUnitCounit (F : C ⥤ D) (G : D ⥤ C) where
  /-- The equivalence between `Hom (F X) Y` and `Hom X (G Y)` coming from an adjunction -/
  homEquiv : ∀ X Y, (F.obj X ⟶ Y) ≃ (X ⟶ G.obj Y)
  /-- The unit of an adjunction -/
  unit : 𝟭 C ⟶ F ⋙ G
  /-- The counit of an adjunction -/
  counit : G ⋙ F ⟶ 𝟭 D
  /-- The relationship between the unit and hom set equivalence of an adjunction -/
  homEquiv_unit : ∀ {X Y f}, (homEquiv X Y) f = unit.app X ≫ G.map f := by aesop_cat
  /-- The relationship between the counit and hom set equivalence of an adjunction -/
  homEquiv_counit : ∀ {X Y g}, (homEquiv X Y).symm g = F.map g ≫ counit.app Y := by aesop_cat

namespace CoreHomEquivUnitCounit

attribute [simp] homEquiv_unit homEquiv_counit

end CoreHomEquivUnitCounit

/-- This is an auxiliary data structure useful for constructing adjunctions.
See `Adjunction.mkOfHomEquiv`.
This structure won't typically be used anywhere else.
-/
-- Porting note(#5171): `has_nonempty_instance` linter not ported yet
-- @[nolint has_nonempty_instance]
structure CoreHomEquiv (F : C ⥤ D) (G : D ⥤ C) where
  /-- The equivalence between `Hom (F X) Y` and `Hom X (G Y)` -/
  homEquiv : ∀ X Y, (F.obj X ⟶ Y) ≃ (X ⟶ G.obj Y)
  /-- The property that describes how `homEquiv.symm` transforms compositions `X' ⟶ X ⟶ G Y` -/
  homEquiv_naturality_left_symm :
    ∀ {X' X Y} (f : X' ⟶ X) (g : X ⟶ G.obj Y),
      (homEquiv X' Y).symm (f ≫ g) = F.map f ≫ (homEquiv X Y).symm g := by
    aesop_cat
  /-- The property that describes how `homEquiv` transforms compositions `F X ⟶ Y ⟶ Y'` -/
  homEquiv_naturality_right :
    ∀ {X Y Y'} (f : F.obj X ⟶ Y) (g : Y ⟶ Y'),
      (homEquiv X Y') (f ≫ g) = (homEquiv X Y) f ≫ G.map g := by
    aesop_cat

namespace CoreHomEquiv

attribute [simp] homEquiv_naturality_left_symm homEquiv_naturality_right

variable {F : C ⥤ D} {G : D ⥤ C} (adj : CoreHomEquiv F G) {X' X : C} {Y Y' : D}

theorem homEquiv_naturality_left (f : X' ⟶ X) (g : F.obj X ⟶ Y) :
    (adj.homEquiv X' Y) (F.map f ≫ g) = f ≫ (adj.homEquiv X Y) g := by
  rw [← Equiv.eq_symm_apply]; simp

theorem homEquiv_naturality_right_symm (f : X ⟶ G.obj Y) (g : Y ⟶ Y') :
    (adj.homEquiv X Y').symm (f ≫ G.map g) = (adj.homEquiv X Y).symm f ≫ g := by
  rw [Equiv.symm_apply_eq]; simp

end CoreHomEquiv

/-- This is an auxiliary data structure useful for constructing adjunctions.
See `Adjunction.mkOfUnitCounit`.
This structure won't typically be used anywhere else.
-/
-- Porting note(#5171): `has_nonempty_instance` linter not ported yet
-- @[nolint has_nonempty_instance]
structure CoreUnitCounit (F : C ⥤ D) (G : D ⥤ C) where
  /-- The unit of an adjunction between `F` and `G` -/
  unit : 𝟭 C ⟶ F.comp G
  /-- The counit of an adjunction between `F` and `G`s -/
  counit : G.comp F ⟶ 𝟭 D
  /-- Equality of the composition of the unit, associator, and counit with the identity
  `F ⟶ (F G) F ⟶ F (G F) ⟶ F = NatTrans.id F` -/
  left_triangle :
    whiskerRight unit F ≫ (Functor.associator F G F).hom ≫ whiskerLeft F counit =
      NatTrans.id (𝟭 C ⋙ F) := by
    aesop_cat
  /-- Equality of the composition of the unit, associator, and counit with the identity
  `G ⟶ G (F G) ⟶ (F G) F ⟶ G = NatTrans.id G` -/
  right_triangle :
    whiskerLeft G unit ≫ (Functor.associator G F G).inv ≫ whiskerRight counit G =
      NatTrans.id (G ⋙ 𝟭 C) := by
    aesop_cat

namespace CoreUnitCounit

attribute [simp] left_triangle right_triangle

end CoreUnitCounit

variable {F : C ⥤ D} {G : D ⥤ C}

@[simps]
def mk' (adj : CoreHomEquivUnitCounit F G) : F ⊣ G where
  unit := adj.unit
  counit := adj.counit
  left_triangle_components X := by
    rw [← adj.homEquiv_counit, (adj.homEquiv _ _).symm_apply_eq]
    simp
  right_triangle_components Y := by
    rw [← adj.homEquiv_unit, ← (adj.homEquiv _ _).eq_symm_apply]
    simp

lemma mk'_homEquiv (adj : CoreHomEquivUnitCounit F G) : (mk' adj).homEquiv = adj.homEquiv := by
  ext; simp

/-- Construct an adjunction between `F` and `G` out of a natural bijection between each
`F.obj X ⟶ Y` and `X ⟶ G.obj Y`. -/
@[simps!]
def mkOfHomEquiv (adj : CoreHomEquiv F G) : F ⊣ G :=
  mk' {
    unit :=
      { app := fun X => (adj.homEquiv X (F.obj X)) (𝟙 (F.obj X))
        naturality := by
          intros
          simp [← adj.homEquiv_naturality_left, ← adj.homEquiv_naturality_right] }
    counit :=
      { app := fun Y => (adj.homEquiv _ _).invFun (𝟙 (G.obj Y))
        naturality := by
          intros
          simp [← adj.homEquiv_naturality_left_symm, ← adj.homEquiv_naturality_right_symm] }
    homEquiv := adj.homEquiv
    homEquiv_unit := fun {X Y f} => by simp [← adj.homEquiv_naturality_right]
    homEquiv_counit := fun {X Y f} => by simp [← adj.homEquiv_naturality_left_symm] }

lemma mkOfHomEquiv_homEquiv (adj : CoreHomEquiv F G) :
    (mkOfHomEquiv adj).homEquiv = adj.homEquiv := by
  ext X Y g
  simp [mkOfHomEquiv, ← adj.homEquiv_naturality_right (𝟙 _) g]

/-- Construct an adjunction between functors `F` and `G` given a unit and counit for the adjunction
satisfying the triangle identities. -/
@[simps!]
def mkOfUnitCounit (adj : CoreUnitCounit F G) : F ⊣ G where
  unit := adj.unit
  counit := adj.counit
  left_triangle_components X := by
    have := adj.left_triangle
    rw [NatTrans.ext_iff, funext_iff] at this
    simpa [-CoreUnitCounit.left_triangle] using this X
  right_triangle_components Y := by
    have := adj.right_triangle
    rw [NatTrans.ext_iff, funext_iff] at this
    simpa [-CoreUnitCounit.right_triangle] using this Y

/-- The adjunction between the identity functor on a category and itself. -/
def id : 𝟭 C ⊣ 𝟭 C where
  unit := 𝟙 _
  counit := 𝟙 _

-- Satisfy the inhabited linter.
instance : Inhabited (Adjunction (𝟭 C) (𝟭 C)) :=
  ⟨id⟩

/-- If F and G are naturally isomorphic functors, establish an equivalence of hom-sets. -/
@[simps]
def equivHomsetLeftOfNatIso {F F' : C ⥤ D} (iso : F ≅ F') {X : C} {Y : D} :
    (F.obj X ⟶ Y) ≃ (F'.obj X ⟶ Y) where
  toFun f := iso.inv.app _ ≫ f
  invFun g := iso.hom.app _ ≫ g
  left_inv f := by simp
  right_inv g := by simp

/-- If G and H are naturally isomorphic functors, establish an equivalence of hom-sets. -/
@[simps]
def equivHomsetRightOfNatIso {G G' : D ⥤ C} (iso : G ≅ G') {X : C} {Y : D} :
    (X ⟶ G.obj Y) ≃ (X ⟶ G'.obj Y) where
  toFun f := f ≫ iso.hom.app _
  invFun g := g ≫ iso.inv.app _
  left_inv f := by simp
  right_inv g := by simp

/-- Transport an adjunction along a natural isomorphism on the left. -/
def ofNatIsoLeft {F G : C ⥤ D} {H : D ⥤ C} (adj : F ⊣ H) (iso : F ≅ G) : G ⊣ H :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y => (equivHomsetLeftOfNatIso iso.symm).trans (adj.homEquiv X Y) }

/-- Transport an adjunction along a natural isomorphism on the right. -/
def ofNatIsoRight {F : C ⥤ D} {G H : D ⥤ C} (adj : F ⊣ G) (iso : G ≅ H) : F ⊣ H :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y => (adj.homEquiv X Y).trans (equivHomsetRightOfNatIso iso) }

-- /-- Transport an adjunction along a natural isomorphism on the left. -/
-- def ofNatIsoLeft {F G : C ⥤ D} {H : D ⥤ C} (adj : F ⊣ H) (iso : F ≅ G) : G ⊣ H where
--   unit := adj.unit ≫ whiskerRight iso.hom _
--   counit := whiskerLeft _ iso.inv ≫ adj.counit
--   right_triangle_components Y := by simp [← H.map_comp_assoc]

-- /-- Transport an adjunction along a natural isomorphism on the right. -/
-- def ofNatIsoRight {F : C ⥤ D} {G H : D ⥤ C} (adj : F ⊣ G) (iso : G ≅ H) : F ⊣ H where
--   unit := adj.unit ≫ whiskerLeft _ iso.hom
--   counit := whiskerRight iso.inv _ ≫ adj.counit
--   left_triangle_components X := by simp [← F.map_comp_assoc]
--   right_triangle_components Y := by
--     simp only [Functor.id_obj, Functor.comp_obj, NatTrans.comp_app, whiskerLeft_app,
--       whiskerRight_app, Functor.map_comp, assoc]
--     rw [← iso.hom.naturality_assoc, ← iso.hom.naturality]
--     simp only [unit_naturality_assoc, right_triangle_components_assoc, Iso.inv_hom_id_app]

-- lemma ofNatIsoLeft_homEquiv {F G : C ⥤ D} {H : D ⥤ C} (adj : F ⊣ H) (iso : F ≅ G) :
--     (adj.ofNatIsoLeft iso).homEquiv = equivHomsetLeftOfNatIso iso := sorry

section

variable {E : Type u₃} [ℰ : Category.{v₃} E] {H : D ⥤ E} {I : E ⥤ D}
  (adj₁ : F ⊣ G) (adj₂ : H ⊣ I)

/-- Composition of adjunctions.

See <https://stacks.math.columbia.edu/tag/0DV0>.
-/
def comp : F ⋙ H ⊣ I ⋙ G :=
  mk' {
    homEquiv := fun _ _ ↦ Equiv.trans (adj₂.homEquiv _ _) (adj₁.homEquiv _ _)
    unit := adj₁.unit ≫ (whiskerLeft F <| whiskerRight adj₂.unit G) ≫ (Functor.associator _ _ _).inv
    counit :=
      (Functor.associator _ _ _).hom ≫ (whiskerLeft I <| whiskerRight adj₁.counit H) ≫ adj₂.counit }

@[reassoc (attr := simp)]
lemma comp_unit_app (X : C) :
    (adj₁.comp adj₂).unit.app X = adj₁.unit.app X ≫ G.map (adj₂.unit.app (F.obj X)) := by
  simp [Adjunction.comp]

@[reassoc (attr := simp)]
lemma comp_counit_app (X : E) :
    (adj₁.comp adj₂).counit.app X = H.map (adj₁.counit.app (I.obj X)) ≫ adj₂.counit.app X := by
  simp [Adjunction.comp]

lemma comp_homEquiv :  (adj₁.comp adj₂).homEquiv =
    fun _ _ ↦ Equiv.trans (adj₂.homEquiv _ _) (adj₁.homEquiv _ _) :=
  mk'_homEquiv _

end

section ConstructLeft

-- Construction of a left adjoint. In order to construct a left
-- adjoint to a functor G : D → C, it suffices to give the object part
-- of a functor F : C → D together with isomorphisms Hom(FX, Y) ≃
-- Hom(X, GY) natural in Y. The action of F on morphisms can be
-- constructed from this data.
variable {F_obj : C → D}
variable (e : ∀ X Y, (F_obj X ⟶ Y) ≃ (X ⟶ G.obj Y))

/-- Construct a left adjoint functor to `G`, given the functor's value on objects `F_obj` and
a bijection `e` between `F_obj X ⟶ Y` and `X ⟶ G.obj Y` satisfying a naturality law
`he : ∀ X Y Y' g h, e X Y' (h ≫ g) = e X Y h ≫ G.map g`.
Dual to `rightAdjointOfEquiv`. -/
@[simps!]
def leftAdjointOfEquiv (he : ∀ X Y Y' g h, e X Y' (h ≫ g) = e X Y h ≫ G.map g) : C ⥤ D where
  obj := F_obj
  map {X} {X'} f := (e X (F_obj X')).symm (f ≫ e X' (F_obj X') (𝟙 _))
  map_comp := fun f f' => by
    rw [Equiv.symm_apply_eq, he, Equiv.apply_symm_apply]
    conv =>
      rhs
      rw [assoc, ← he, id_comp, Equiv.apply_symm_apply]
    simp

variable (he : ∀ X Y Y' g h, e X Y' (h ≫ g) = e X Y h ≫ G.map g)

/-- Show that the functor given by `leftAdjointOfEquiv` is indeed left adjoint to `G`. Dual
to `adjunctionOfRightEquiv`. -/
@[simps!]
def adjunctionOfEquivLeft : leftAdjointOfEquiv e he ⊣ G :=
  mkOfHomEquiv
    { homEquiv := e
      homEquiv_naturality_left_symm := fun {X'} {X} {Y} f g => by
        have {X : C} {Y Y' : D} (f : X ⟶ G.obj Y) (g : Y ⟶ Y') :
            (e X Y').symm (f ≫ G.map g) = (e X Y).symm f ≫ g := by
          rw [Equiv.symm_apply_eq, he]; simp
        simp [← this, ← Equiv.apply_eq_iff_eq (e X' Y), ← he] }

end ConstructLeft

section ConstructRight

-- Construction of a right adjoint, analogous to the above.
variable {G_obj : D → C}
variable (e : ∀ X Y, (F.obj X ⟶ Y) ≃ (X ⟶ G_obj Y))

private theorem he'' (he : ∀ X' X Y f g, e X' Y (F.map f ≫ g) = f ≫ e X Y g)
    {X' X Y} (f g) : F.map f ≫ (e X Y).symm g = (e X' Y).symm (f ≫ g) := by
  rw [Equiv.eq_symm_apply, he]; simp

/-- Construct a right adjoint functor to `F`, given the functor's value on objects `G_obj` and
a bijection `e` between `F.obj X ⟶ Y` and `X ⟶ G_obj Y` satisfying a naturality law
`he : ∀ X Y Y' g h, e X' Y (F.map f ≫ g) = f ≫ e X Y g`.
Dual to `leftAdjointOfEquiv`. -/
@[simps!]
def rightAdjointOfEquiv (he : ∀ X' X Y f g, e X' Y (F.map f ≫ g) = f ≫ e X Y g) : D ⥤ C where
  obj := G_obj
  map {Y} {Y'} g := (e (G_obj Y) Y') ((e (G_obj Y) Y).symm (𝟙 _) ≫ g)
  map_comp := fun {Y} {Y'} {Y''} g g' => by
    rw [← Equiv.eq_symm_apply, ← he'' e he, Equiv.symm_apply_apply]
    conv =>
      rhs
      rw [← assoc, he'' e he, comp_id, Equiv.symm_apply_apply]
    simp

/-- Show that the functor given by `rightAdjointOfEquiv` is indeed right adjoint to `F`. Dual
to `adjunctionOfEquivRight`. -/
@[simps!]
def adjunctionOfEquivRight (he : ∀ X' X Y f g, e X' Y (F.map f ≫ g) = f ≫ e X Y g) :
    F ⊣ (rightAdjointOfEquiv e he) :=
  mkOfHomEquiv
    { homEquiv := e
      homEquiv_naturality_left_symm := by
        intro X X' Y f g; rw [Equiv.symm_apply_eq]; simp [he]
      homEquiv_naturality_right := by
        intro X Y Y' g h
        simp [← he, reassoc_of% (he'' e)] }

end ConstructRight

/--
If the unit and counit of a given adjunction are (pointwise) isomorphisms, then we can upgrade the
adjunction to an equivalence.
-/
@[simps!]
noncomputable def toEquivalence (adj : F ⊣ G) [∀ X, IsIso (adj.unit.app X)]
    [∀ Y, IsIso (adj.counit.app Y)] : C ≌ D where
  functor := F
  inverse := G
  unitIso := NatIso.ofComponents fun X => asIso (adj.unit.app X)
  counitIso := NatIso.ofComponents fun Y => asIso (adj.counit.app Y)

end Adjunction

open Adjunction

/--
If the unit and counit for the adjunction corresponding to a right adjoint functor are (pointwise)
isomorphisms, then the functor is an equivalence of categories.
-/
lemma Functor.isEquivalence_of_isRightAdjoint (G : C ⥤ D) [IsRightAdjoint G]
    [∀ X, IsIso ((Adjunction.ofIsRightAdjoint G).unit.app X)]
    [∀ Y, IsIso ((Adjunction.ofIsRightAdjoint G).counit.app Y)] : G.IsEquivalence :=
  (Adjunction.ofIsRightAdjoint G).toEquivalence.isEquivalence_inverse

namespace Equivalence

variable (e : C ≌ D)

/-- The adjunction given by an equivalence of categories. (To obtain the opposite adjunction,
simply use `e.symm.toAdjunction`. -/
@[simps! unit counit]
def toAdjunction : e.functor ⊣ e.inverse :=
  ⟨e.unit, e.counit, by simp, by simp⟩

lemma isLeftAdjoint_functor : e.functor.IsLeftAdjoint where
  exists_rightAdjoint := ⟨_, ⟨e.toAdjunction⟩⟩

lemma isRightAdjoint_inverse : e.inverse.IsRightAdjoint where
  exists_leftAdjoint := ⟨_, ⟨e.toAdjunction⟩⟩

lemma isLeftAdjoint_inverse : e.inverse.IsLeftAdjoint :=
  e.symm.isLeftAdjoint_functor

lemma isRightAdjoint_functor : e.functor.IsRightAdjoint :=
  e.symm.isRightAdjoint_inverse

end Equivalence

namespace Functor

/-- If `F` and `G` are left adjoints then `F ⋙ G` is a left adjoint too. -/
instance isLeftAdjoint_comp {E : Type u₃} [Category.{v₃} E] (F : C ⥤ D) (G : D ⥤ E)
    [F.IsLeftAdjoint] [G.IsLeftAdjoint] : (F ⋙ G).IsLeftAdjoint where
  exists_rightAdjoint :=
    ⟨_, ⟨(Adjunction.ofIsLeftAdjoint F).comp (Adjunction.ofIsLeftAdjoint G)⟩⟩

/-- If `F` and `G` are right adjoints then `F ⋙ G` is a right adjoint too. -/
instance isRightAdjoint_comp {E : Type u₃} [Category.{v₃} E] {F : C ⥤ D} {G : D ⥤ E}
    [IsRightAdjoint F] [IsRightAdjoint G] : IsRightAdjoint (F ⋙ G) where
  exists_leftAdjoint :=
    ⟨_, ⟨(Adjunction.ofIsRightAdjoint G).comp (Adjunction.ofIsRightAdjoint F)⟩⟩

/-- Transport being a right adjoint along a natural isomorphism. -/
lemma isRightAdjoint_of_iso {F G : C ⥤ D} (h : F ≅ G) [F.IsRightAdjoint] :
    IsRightAdjoint G where
  exists_leftAdjoint := ⟨_, ⟨(Adjunction.ofIsRightAdjoint F).ofNatIsoRight h⟩⟩

/-- Transport being a left adjoint along a natural isomorphism. -/
lemma isLeftAdjoint_of_iso {F G : C ⥤ D} (h : F ≅ G) [IsLeftAdjoint F] :
    IsLeftAdjoint G where
  exists_rightAdjoint := ⟨_, ⟨(Adjunction.ofIsLeftAdjoint F).ofNatIsoLeft h⟩⟩


/-- An equivalence `E` is left adjoint to its inverse. -/
noncomputable def adjunction (E : C ⥤ D) [IsEquivalence E] : E ⊣ E.inv :=
  E.asEquivalence.toAdjunction

/-- If `F` is an equivalence, it's a left adjoint. -/
instance (priority := 10) isLeftAdjoint_of_isEquivalence {F : C ⥤ D} [F.IsEquivalence] :
    IsLeftAdjoint F :=
  F.asEquivalence.isLeftAdjoint_functor

/-- If `F` is an equivalence, it's a right adjoint. -/
instance (priority := 10) isRightAdjoint_of_isEquivalence {F : C ⥤ D} [F.IsEquivalence] :
    IsRightAdjoint F :=
  F.asEquivalence.isRightAdjoint_functor

end Functor

end CategoryTheory
