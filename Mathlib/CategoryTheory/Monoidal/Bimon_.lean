/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.CategoryTheory.Monoidal.Comon_

/-!
# The category of bimonoids in a braided monoidal category.

We define bimonoids in a braided monoidal category `C`
as comonoid objects in the category of monoid objects in `C`.

We verify that this is equivalent to the monoid objects in the category of comonoid objects.

## TODO
* Define Hopf monoids, which in a cartesian monoidal category are exactly group objects,
  and use this to define group schemes.
* Construct the category of modules, and show that it is monoidal with a monoidal forgetful functor
  to `C`.
* Relax the requirement that `C` is braided, instead requiring that the structure morphisms are
  central. This would require completely replacing the definition.
* Some form of Tannaka reconstruction: given a central monoidal functor `F : C ⥤ D`,
  the internal endomorphisms of `F` form a bimonoid in presheaves on `D`,
  in good circumstances this is representable by a bimonoid in `D`, and then
  `C` is monoidally equivalent to the modules over that bimonoid.
-/

noncomputable section

universe v₁ v₂ u₁ u₂ u

open CategoryTheory MonoidalCategory

variable (C : Type u₁) [Category.{v₁} C] [MonoidalCategory.{v₁} C] [BraidedCategory C]

/--
A bimonoid object in a braided category `C` is a comonoid object in the (monoidal)
category of monoid objects in `C`.
-/
def Bimon_ := Comon_ (Mon_ C)

namespace Bimon_

instance : Category (Bimon_ C) := inferInstanceAs (Category (Comon_ (Mon_ C)))

@[ext] lemma ext {X Y : Bimon_ C} {f g : X ⟶ Y} (w : f.hom.hom = g.hom.hom) : f = g :=
  Comon_.Hom.ext _ _ (Mon_.Hom.ext _ _ w)

@[simp] theorem id_hom' (M : Bimon_ C) : Comon_.Hom.hom (𝟙 M) = 𝟙 M.X := rfl

@[simp]
theorem comp_hom' {M N K : Bimon_ C} (f : M ⟶ N) (g : N ⟶ K) : (f ≫ g).hom = f.hom ≫ g.hom :=
  rfl

/-- The forgetful functor from bimonoid objects to monoid objects. -/
abbrev toMon_ : Bimon_ C ⥤ Mon_ C := Comon_.forget (Mon_ C)

/-- The forgetful functor from bimonoid objects to the underlying category. -/
def forget : Bimon_ C ⥤ C := toMon_ C ⋙ Mon_.forget C

@[simp]
theorem toMon_forget : toMon_ C ⋙ Mon_.forget C = forget C := rfl

/-- The forgetful functor from bimonoid objects to comonoid objects. -/
@[simps!]
def toComon_ : Bimon_ C ⥤ Comon_ C := (Mon_.forgetMonoidal C).toOplaxMonoidalFunctor.mapComon

@[simp]
theorem toComon_forget : toComon_ C ⋙ Comon_.forget C = forget C := rfl

/-- The object level part of the forward direction of `Comon_ (Mon_ C) ≌ Mon_ (Comon_ C)` -/
def toMon_Comon_obj (M : Bimon_ C) : Mon_ (Comon_ C) where
  X := (toComon_ C).obj M
  one := { hom := M.X.one }
  mul :=
  { hom := M.X.mul,
    hom_comul := by dsimp; simp [tensor_μ] }

attribute [simps] toMon_Comon_obj -- We add this after the fact to avoid a timeout.

/-- The forward direction of `Comon_ (Mon_ C) ≌ Mon_ (Comon_ C)` -/
@[simps]
def toMon_Comon_ : Bimon_ C ⥤ Mon_ (Comon_ C) where
  obj := toMon_Comon_obj C
  map f :=
  { hom := (toComon_ C).map f }

/-- The object level part of the backward direction of `Comon_ (Mon_ C) ≌ Mon_ (Comon_ C)` -/
@[simps]
def ofMon_Comon_obj (M : Mon_ (Comon_ C)) : Bimon_ C where
  X := (Comon_.forgetMonoidal C).toLaxMonoidalFunctor.mapMon.obj M
  counit := { hom := M.X.counit }
  comul :=
  { hom := M.X.comul,
    mul_hom := by dsimp; simp [tensor_μ] }

/-- The backward direction of `Comon_ (Mon_ C) ≌ Mon_ (Comon_ C)` -/
@[simps]
def ofMon_Comon_ : Mon_ (Comon_ C) ⥤ Bimon_ C where
  obj := ofMon_Comon_obj C
  map f :=
  { hom := (Comon_.forgetMonoidal C).toLaxMonoidalFunctor.mapMon.map f }

/-- The equivalence `Comon_ (Mon_ C) ≌ Mon_ (Comon_ C)` -/
def equivMon_Comon_ : Bimon_ C ≌ Mon_ (Comon_ C) where
  functor := toMon_Comon_ C
  inverse := ofMon_Comon_ C
  unitIso := NatIso.ofComponents (fun _ => Comon_.mkIso (Mon_.mkIso (Iso.refl _)))
  counitIso := NatIso.ofComponents (fun _ => Mon_.mkIso (Comon_.mkIso (Iso.refl _)))

/-! # Additional simp lemmas -/

@[reassoc (attr := simp)] theorem comul_counit_hom (M : Bimon_ C) :
    M.comul.hom ≫ (_ ◁ M.counit.hom) = (ρ_ _).inv := by
  simpa [- Comon_.comul_counit] using congr_arg Mon_.Hom.hom M.comul_counit

@[reassoc (attr := simp)] theorem counit_comul_hom (M : Bimon_ C) :
    M.comul.hom ≫ (M.counit.hom ▷ _) = (λ_ _).inv := by
  simpa [- Comon_.counit_comul] using congr_arg Mon_.Hom.hom M.counit_comul

@[reassoc (attr := simp)] theorem comul_assoc_hom (M : Bimon_ C) :
    M.comul.hom ≫ (M.X.X ◁ M.comul.hom) =
      M.comul.hom ≫ (M.comul.hom ▷ M.X.X) ≫ (α_ M.X.X M.X.X M.X.X).hom := by
  simpa [- Comon_.comul_assoc] using congr_arg Mon_.Hom.hom M.comul_assoc

@[reassoc] theorem comul_assoc_flip_hom (M : Bimon_ C) :
    M.comul.hom ≫ (M.comul.hom ▷ M.X.X) =
      M.comul.hom ≫ (M.X.X ◁ M.comul.hom) ≫ (α_ M.X.X M.X.X M.X.X).inv := by
  simp

/-! # The convolution monoid of a pair of bimonoids. -/

variable {C}

/--
The morphisms in `C` between the underlying objects of a pair of bimonoids in `C` naturally has a
(set-theoretic) monoid structure. -/
def Conv (M N : Bimon_ C) : Type v₁ := M.X.X ⟶ N.X.X

variable {M N : Bimon_ C}

instance : One (Conv M N) where
  one := M.counit.hom ≫ N.X.one

@[simp] theorem one_eq : (1 : Conv M N) = M.counit.hom ≫ N.X.one := rfl

instance : Mul (Conv M N) where
  mul := fun f g => M.comul.hom ≫ f ▷ M.X.X ≫ N.X.X ◁ g ≫ N.X.mul

@[simp] theorem mul_eq (f g : Conv M N) : f * g = M.comul.hom ≫ f ▷ M.X.X ≫ N.X.X ◁ g ≫ N.X.mul := rfl

instance : Monoid (Conv M N) where
  one_mul f := by simp [← whisker_exchange_assoc]
  mul_one f := by simp [← whisker_exchange_assoc]
  mul_assoc f g h := by
    simp only [mul_eq]
    simp only [comp_whiskerRight, whisker_assoc, Category.assoc,
      MonoidalCategory.whiskerLeft_comp]
    slice_lhs 7 8 =>
      rw [← whisker_exchange]
    slice_rhs 2 3 =>
      rw [← whisker_exchange]
    slice_rhs 1 2 =>
      rw [M.comul_assoc_hom]
    simp only [Mon_.monMonoidalStruct_tensorObj_X]
    slice_rhs 3 4 =>
      rw [← associator_naturality_left]
    slice_lhs 6 7 =>
      rw [← associator_inv_naturality_right]
    slice_lhs 8 9 =>
      rw [N.X.mul_assoc]
    simp

end Bimon_
