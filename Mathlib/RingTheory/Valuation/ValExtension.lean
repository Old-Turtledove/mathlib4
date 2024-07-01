/-
Copyright (c) 2024 Jiedong Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Bichang Lei
-/
import Mathlib.RingTheory.Valuation.Integers
import Mathlib.RingTheory.Ideal.LocalRing

/-!
# Extension of Valuation

In this file, we define the typeclass for valuation extensions and prove basic facts about
extension of valuations. Let `A` be an `R` algebra, equipped with valuation `vA` and `vR`
respectively. Here, extension of valuation means that the pullback of valuation `vA` to `R` is
equivalent to the valuation `vR` on `R`. We only require equivalence, not equality of valuations
here.

Note that we do not require the ring map from `R` to `A` to be injective. It holds automatically
when `R` is a division ring and `A` is nontrivial.

## Main Definition

* `IsValExtension vR vA` : The valuation `vA` on `A` is an extension of the valuation `vR` on `R`.

## References

* [Bourbaki, Nicolas. *Commutative algebra*] Chapter VI §3, Valuations.
* <https://en.wikipedia.org/wiki/Valuation_(algebra)#Extension_of_valuations>

## Tags
Valuation, Extension of Valuation

-/
open Valuation

variable {R K A ΓR ΓK ΓA : Type*} [CommRing R] [Field K] [Ring A]
    [LinearOrderedCommMonoidWithZero ΓR] [LinearOrderedCommMonoidWithZero ΓK]
    [LinearOrderedCommMonoidWithZero ΓA] [Algebra R A] [Algebra K A]
    (vR : Valuation R ΓR) (vK : Valuation K ΓK) (vA : Valuation A ΓA)

/--
The class `IsValExtension R A` states that the valuation of `A` is an extension of the valuation
on `R`. More precisely, the valuation on `R` is equivlent to the comap of the valuation on `A`.
-/
class IsValExtension : Prop where
  /-- The valuation on `R` is equivlent to the comap of the valuation on `A` -/
  val_isEquiv_comap : vR.IsEquiv <| vA.comap (algebraMap R A)

namespace IsValExtension

section CoeLemma

variable [IsValExtension vR vA]

-- @[simp] does not work because `vR` cannot be inferred from `R`.
theorem val_map_le_iff (x y : R) : vA (algebraMap R A x) ≤ vA (algebraMap R A y) ↔ vR x ≤ vR y :=
  (val_isEquiv_comap).symm

theorem val_map_lt_iff (x y : R) : vA (algebraMap R A x) < vA (algebraMap R A y) ↔ vR x < vR y :=
  (IsEquiv.val_lt val_isEquiv_comap).symm

theorem val_map_eq_iff (x y : R) : vA (algebraMap R A x) = vA (algebraMap R A y) ↔ vR x = vR y :=
  (IsEquiv.val_eq val_isEquiv_comap).symm

theorem val_map_le_one_iff (x : R) : vA (algebraMap R A x) ≤ 1 ↔ vR x ≤ 1 :=
  (IsEquiv.val_le_one val_isEquiv_comap).symm

theorem val_map_lt_one_iff (x : R) : vA (algebraMap R A x) < 1 ↔ vR x < 1 :=
  (IsEquiv.val_lt_one val_isEquiv_comap).symm

theorem val_map_eq_one_iff (x : R) : vA (algebraMap R A x) = 1 ↔ vR x = 1 :=
  (IsEquiv.val_eq_one val_isEquiv_comap).symm

instance id : IsValExtension vR vR where
  val_isEquiv_comap := by
    simp only [Algebra.id.map_eq_id, comap_id]
    rfl

end CoeLemma

variable {ΓR ΓA ΓK: Type*} [LinearOrderedCommGroupWithZero ΓR] [LinearOrderedCommGroupWithZero ΓK]
    [LinearOrderedCommGroupWithZero ΓA] {vR : Valuation R ΓR} {vK : Valuation K ΓK}
    {vA : Valuation A ΓA} [IsValExtension vR vA] [IsValExtension vK vA]

section mk'

/--
When `K` is a field, if the preimage of the valuation integers of `A` equals to the valuation
integers of `K`, then the valuation on `A` is an extension of valuation on `K`.
-/
theorem ofComapInteger (h : vA.integer.comap (algebraMap K A) = vK.integer) :
    IsValExtension vK vA where
  val_isEquiv_comap := by
    rw [isEquiv_iff_val_le_one]
    intro x
    rw [← Valuation.mem_integer_iff, ← Valuation.mem_integer_iff, ← h]
    rfl

end mk'

section integer

instance instAlgebraInteger : Algebra vR.integer vA.integer where
  smul r a := ⟨r • a,
    Algebra.smul_def r (a : A) ▸ mul_mem ((val_map_le_one_iff vR vA _).mpr r.2) a.2⟩
  __ := (algebraMap R A).restrict vR.integer vA.integer
    (by simp [Valuation.mem_integer_iff, val_map_le_one_iff vR vA])
  commutes' _ _ := Subtype.ext (Algebra.commutes _ _)
  smul_def' _ _ := Subtype.ext (Algebra.smul_def _ _)

@[simp, norm_cast]
theorem val_smul (r : vR.integer) (a : vA.integer) : ↑(r • a : vA.integer) = (r : R) • (a : A) := by
  rfl

@[simp, norm_cast]
theorem val_algebraMap (r : vR.integer) :
    ((algebraMap vR.integer vA.integer) r : A) = (algebraMap R A) (r : R) := by
  rfl

instance instIsScalarTowerInteger : IsScalarTower vR.integer vA.integer A where
  smul_assoc x y z := by
    simp only [Algebra.smul_def]
    exact mul_assoc _ _ _

instance instNoZeroSMulDivisorsInteger [NoZeroSMulDivisors R A] :
    NoZeroSMulDivisors vR.integer vA.integer := by
  refine ⟨fun {x y} e ↦ ?_⟩
  have : (x : R) • (y : A) = 0 := by simpa [Subtype.ext_iff, Algebra.smul_def] using e
  simpa only [Subtype.ext_iff, smul_eq_zero] using this

theorem algebraMap_injective [Nontrivial A] :
    Function.Injective (algebraMap vK.integer vA.integer) := by
  intro x y h
  simp only [Subtype.ext_iff, val_algebraMap] at h
  ext
  apply RingHom.injective (algebraMap K A) h

instance instIsLocalRingHomValuationInteger {S ΓS: Type*} [CommRing S]
    [LinearOrderedCommGroupWithZero ΓS]
    [Algebra R S] [IsLocalRingHom (algebraMap R S)] {vS : Valuation S ΓS}
    [IsValExtension vR vS] : IsLocalRingHom (algebraMap vR.integer vS.integer) where
  map_nonunit r hr := by
    apply (Valuation.integer.integers (v := vR)).isUnit_of_one
    · exact (isUnit_map_iff (algebraMap R S) _).mp (hr.map (algebraMap _ S))
    · apply (Valuation.integer.integers (v := vS)).one_of_isUnit at hr
      exact (val_map_eq_one_iff vR vS _).mp hr

end integer

end IsValExtension
