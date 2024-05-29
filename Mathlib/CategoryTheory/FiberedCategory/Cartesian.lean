/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau, Calle Sönne
-/

import Mathlib.CategoryTheory.FiberedCategory.HomLift

/-!

# Cartesian morphisms

This file defines cartesian resp. strongly cartesian morphisms in a based category.

## Main definitions
- `IsCartesian p f φ` expresses that `φ` is a cartesian arrow lying over `f` with respect to `p`.
This structure extends `IsHomLift p f φ`.

## References
* [A. Grothendieck, M. Raynaud, *SGA 1*](https://arxiv.org/abs/math/0206203)
-/

universe v₁ v₂ u₁ u₂

open CategoryTheory Functor Category IsHomLift

namespace CategoryTheory

variable {𝒮 : Type u₁} {𝒳 : Type u₂} [Category.{v₁} 𝒮] [Category.{v₂} 𝒳]

/-- The proposition that a lift
```
  a --φ--> b
  -        -
  |        |
  v        v
  R --f--> S
```
is a cartesian arrow, see SGA 1 VI 5.1.
-/
class Functor.IsCartesian (p : 𝒳 ⥤ 𝒮) {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) extends
    IsHomLift p f φ : Prop where
  universal_property {a' : 𝒳} (φ' : a' ⟶ b) [IsHomLift p f φ'] :
      ∃! χ : a' ⟶ a, IsHomLift p (𝟙 R) χ ∧ χ ≫ φ = φ'

namespace IsCartesian

/-- Given an arrow `φ' : a' ⟶ b` and a diagram:
```
a'        a --φ--> b
|         |        |
v         v        v
R' ====== R --f--> S
```
such that `φ` is a cartesian arrow, then `inducedMap f φ φ'` is the map `a' ⟶ a`
obtained from the universal property of `φ`. -/
noncomputable def inducedMap (p : 𝒳 ⥤ 𝒮) {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b)
    [IsCartesian p f φ] {a' : 𝒳} (φ' : a' ⟶ b) [IsHomLift p f φ'] : a' ⟶ a :=
  Classical.choose <| IsCartesian.universal_property (p:=p) (f:=f) (φ:=φ) φ'

instance inducedMap_isHomLift (p : 𝒳 ⥤ 𝒮) {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b)
    [IsCartesian p f φ] {a' : 𝒳} (φ' : a' ⟶ b) [IsHomLift p f φ'] :
      IsHomLift p (𝟙 R) (inducedMap p f φ φ') :=
  (Classical.choose_spec <| IsCartesian.universal_property (p:=p) (f:=f) (φ:=φ) φ').1.1

@[simp]
lemma inducedMap_comp (p : 𝒳 ⥤ 𝒮) {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b)
    [IsCartesian p f φ] {a' : 𝒳} (φ' : a' ⟶ b) [IsHomLift p f φ'] :
      (inducedMap p f φ φ') ≫ φ = φ' :=
  (Classical.choose_spec <| IsCartesian.universal_property (p:=p) (f:=f) (φ:=φ) φ').1.2

/-- Given a diagram:
```
a'        a --φ--> b
|         |        |
v         v        v
R' ====== R --f--> S
```
with `φ` a cartesian arrow. Then for any morphism `φ' : a' ⟶ b`, and any `ψ : a' ⟶ a` such that
`g ≫ ψ = φ'`. Then `ψ` equals the map induced by the universal property of `φ`. -/
lemma inducedMap_unique (p : 𝒳 ⥤ 𝒮) {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b)
    [IsCartesian p f φ] {a' : 𝒳} (φ' : a' ⟶ b) [IsHomLift p f φ']
    (ψ : a' ⟶ a) [IsHomLift p (𝟙 R) ψ] (hψ : ψ ≫ φ = φ') : ψ = inducedMap p f φ φ' :=
  (Classical.choose_spec <| IsCartesian.universal_property (p:=p) (f:=f) (φ:=φ) φ').2
    ψ ⟨inferInstance, hψ⟩

/-- Given a diagram a cartesian arrow `φ : a ⟶ b` in `𝒳` and a diagram
```
a'        a --φ--> b
|         |        |
v         v        v
R' ====== R --f--> S
```
Then for any arrow `φ' : a' ⟶ b`, and any two arrows `ψ ψ' : a' ⟶ a` such that
`g ≫ ψ = φ' = g ≫ ψ'`. Then we must have `ψ = ψ'`. -/
protected lemma uniqueness (p : 𝒳 ⥤ 𝒮) {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b)
    [IsCartesian p f φ] {a' : 𝒳} (φ' : a' ⟶ b) [IsHomLift p f φ'] {ψ ψ' : a' ⟶ a}
    [IsHomLift p (𝟙 R) ψ] [IsHomLift p (𝟙 R) ψ'] (hcomp : ψ ≫ φ = φ') (hcomp' : ψ' ≫ φ = φ') :
      ψ = ψ' := by
  rw [inducedMap_unique p f φ φ' ψ hcomp, inducedMap_unique p f φ φ' ψ' hcomp']

@[simp]
lemma inducedMap_self_eq_id (p : 𝒳 ⥤ 𝒮) {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b)
    [IsCartesian p f φ] : inducedMap p f φ φ = 𝟙 a := by
  subst_hom_lift p f φ; symm
  apply inducedMap_unique
  simp only [id_comp]

/-- The canonical isomorphism between the domains of two cartesian arrows
lying over the same object. -/
@[simps]
noncomputable def naturalIso (p : 𝒳 ⥤ 𝒮) {R S : 𝒮} {a' a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b)
    (φ' : a' ⟶ b) [IsCartesian p f φ] [IsCartesian p f φ'] : a' ≅ a where
  hom := inducedMap p f φ φ'
  inv := inducedMap p f φ' φ
  -- TODO: simplify
  hom_inv_id := by
    have : p.IsHomLift (𝟙 R) (𝟙 a') := by apply IsHomLift.id (domain_eq p f φ')
    apply IsCartesian.uniqueness p f φ' φ' (by simp) (id_comp _)
  inv_hom_id := by
    have : p.IsHomLift (𝟙 R) (𝟙 a) := by apply IsHomLift.id (domain_eq p f φ)
    apply IsCartesian.uniqueness p f φ φ (by simp) (id_comp _)

-- TODO: naturalIso API

end IsCartesian
