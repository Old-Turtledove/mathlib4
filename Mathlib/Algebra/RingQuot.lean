/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Algebra.Algebra.Hom
import Mathlib.RingTheory.Ideal.Quotient

/-!
# Quotients of non-commutative rings

Unfortunately, ideals have only been developed in the commutative case as `Ideal`,
and it's not immediately clear how one should formalise ideals in the non-commutative case.

In this file, we directly define the quotient of a semiring by any relation,
by building a bigger relation that represents the ideal generated by that relation.

We prove the universal properties of the quotient, and recommend avoiding relying on the actual
definition, which is made irreducible for this purpose.

Since everything runs in parallel for quotients of `R`-algebras, we do that case at the same time.
-/

assert_not_exists Star.star

universe uR uS uT uA u₄

variable {R : Type uR} [Semiring R]
variable {S : Type uS} [CommSemiring S]
variable {T : Type uT}
variable {A : Type uA} [Semiring A] [Algebra S A]

namespace RingCon

instance (c : RingCon A) : Algebra S c.Quotient where
  smul := (· • ·)
  toRingHom := c.mk'.comp (algebraMap S A)
  commutes' _ := Quotient.ind' fun _ ↦ congr_arg Quotient.mk'' <| Algebra.commutes _ _
  smul_def' _ := Quotient.ind' fun _ ↦ congr_arg Quotient.mk'' <| Algebra.smul_def _ _

@[simp, norm_cast]
theorem coe_algebraMap (c : RingCon A) (s : S) :
    (algebraMap S A s : c.Quotient) = algebraMap S _ s :=
  rfl

end RingCon

namespace RingQuot

/-- Given an arbitrary relation `r` on a ring, we strengthen it to a relation `Rel r`,
such that the equivalence relation generated by `Rel r` has `x ~ y` if and only if
`x - y` is in the ideal generated by elements `a - b` such that `r a b`.
-/
inductive Rel (r : R → R → Prop) : R → R → Prop
  | of ⦃x y : R⦄ (h : r x y) : Rel r x y
  | add_left ⦃a b c⦄ : Rel r a b → Rel r (a + c) (b + c)
  | mul_left ⦃a b c⦄ : Rel r a b → Rel r (a * c) (b * c)
  | mul_right ⦃a b c⦄ : Rel r b c → Rel r (a * b) (a * c)

theorem Rel.add_right {r : R → R → Prop} ⦃a b c : R⦄ (h : Rel r b c) : Rel r (a + b) (a + c) := by
  rw [add_comm a b, add_comm a c]
  exact Rel.add_left h

theorem Rel.neg {R : Type uR} [Ring R] {r : R → R → Prop} ⦃a b : R⦄ (h : Rel r a b) :
    Rel r (-a) (-b) := by simp only [neg_eq_neg_one_mul a, neg_eq_neg_one_mul b, Rel.mul_right h]

theorem Rel.sub_left {R : Type uR} [Ring R] {r : R → R → Prop} ⦃a b c : R⦄ (h : Rel r a b) :
    Rel r (a - c) (b - c) := by simp only [sub_eq_add_neg, h.add_left]

theorem Rel.sub_right {R : Type uR} [Ring R] {r : R → R → Prop} ⦃a b c : R⦄ (h : Rel r b c) :
    Rel r (a - b) (a - c) := by simp only [sub_eq_add_neg, h.neg.add_right]

theorem Rel.smul {r : A → A → Prop} (k : S) ⦃a b : A⦄ (h : Rel r a b) : Rel r (k • a) (k • b) := by
  simp only [Algebra.smul_def, Rel.mul_right h]

/-- `EqvGen (RingQuot.Rel r)` is a ring congruence. -/
def ringCon (r : R → R → Prop) : RingCon R where
  r := EqvGen (Rel r)
  iseqv := EqvGen.is_equivalence _
  add' {a b c d} hab hcd := by
    induction hab generalizing c d with
    | rel _ _ hab =>
      refine (EqvGen.rel _ _ hab.add_left).trans _ _ _ ?_
      induction hcd with
      | rel _ _ hcd => exact EqvGen.rel _ _ hcd.add_right
      | refl => exact EqvGen.refl _
      | symm _ _ _ h => exact h.symm _ _
      | trans _ _ _ _ _ h h' => exact h.trans _ _ _ h'
    | refl => induction hcd with
      | rel _ _ hcd => exact EqvGen.rel _ _ hcd.add_right
      | refl => exact EqvGen.refl _
      | symm _ _ _ h => exact h.symm _ _
      | trans _ _ _ _ _ h h' => exact h.trans _ _ _ h'
    | symm x y _ hxy => exact (hxy hcd.symm).symm
    | trans x y z _ _ h h' => exact (h hcd).trans _ _ _ (h' <| EqvGen.refl _)
  mul' {a b c d} hab hcd := by
    induction hab generalizing c d with
    | rel _ _ hab =>
      refine (EqvGen.rel _ _ hab.mul_left).trans _ _ _ ?_
      induction hcd with
      | rel _ _ hcd => exact EqvGen.rel _ _ hcd.mul_right
      | refl => exact EqvGen.refl _
      | symm _ _ _ h => exact h.symm _ _
      | trans _ _ _ _ _ h h' => exact h.trans _ _ _ h'
    | refl => induction hcd with
      | rel _ _ hcd => exact EqvGen.rel _ _ hcd.mul_right
      | refl => exact EqvGen.refl _
      | symm _ _ _ h => exact h.symm _ _
      | trans _ _ _ _ _ h h' => exact h.trans _ _ _ h'
    | symm x y _ hxy => exact (hxy hcd.symm).symm
    | trans x y z _ _ h h' => exact (h hcd).trans _ _ _ (h' <| EqvGen.refl _)

theorem eqvGen_rel_eq (r : R → R → Prop) : EqvGen (Rel r) = RingConGen.Rel r := by
  ext x₁ x₂
  constructor
  · intro h
    induction h with
    | rel _ _ h => induction h with
      | of => exact RingConGen.Rel.of _ _ ‹_›
      | add_left _ h => exact h.add (RingConGen.Rel.refl _)
      | mul_left _ h => exact h.mul (RingConGen.Rel.refl _)
      | mul_right _ h => exact (RingConGen.Rel.refl _).mul h
    | refl => exact RingConGen.Rel.refl _
    | symm => exact RingConGen.Rel.symm ‹_›
    | trans => exact RingConGen.Rel.trans ‹_› ‹_›
  · intro h
    induction h with
    | of => exact EqvGen.rel _ _ (Rel.of ‹_›)
    | refl => exact (RingQuot.ringCon r).refl _
    | symm => exact (RingQuot.ringCon r).symm ‹_›
    | trans => exact (RingQuot.ringCon r).trans ‹_› ‹_›
    | add => exact (RingQuot.ringCon r).add ‹_› ‹_›
    | mul => exact (RingQuot.ringCon r).mul ‹_› ‹_›

end RingQuot

/-- The quotient of a ring by an arbitrary relation. -/
structure RingQuot (r : R → R → Prop) where
  toQuot : Quot (RingQuot.Rel r)

namespace RingQuot

variable (r : R → R → Prop)

-- can't be irreducible, causes diamonds in ℕ-algebras
private def natCast (n : ℕ) : RingQuot r :=
  ⟨Quot.mk _ n⟩

private irreducible_def zero : RingQuot r :=
  ⟨Quot.mk _ 0⟩

private irreducible_def one : RingQuot r :=
  ⟨Quot.mk _ 1⟩

private irreducible_def add : RingQuot r → RingQuot r → RingQuot r
  | ⟨a⟩, ⟨b⟩ => ⟨Quot.map₂ (· + ·) Rel.add_right Rel.add_left a b⟩

private irreducible_def mul : RingQuot r → RingQuot r → RingQuot r
  | ⟨a⟩, ⟨b⟩ => ⟨Quot.map₂ (· * ·) Rel.mul_right Rel.mul_left a b⟩

private irreducible_def neg {R : Type uR} [Ring R] (r : R → R → Prop) : RingQuot r → RingQuot r
  | ⟨a⟩ => ⟨Quot.map (fun a ↦ -a) Rel.neg a⟩

private irreducible_def sub {R : Type uR} [Ring R] (r : R → R → Prop) :
  RingQuot r → RingQuot r → RingQuot r
  | ⟨a⟩, ⟨b⟩ => ⟨Quot.map₂ Sub.sub Rel.sub_right Rel.sub_left a b⟩

private irreducible_def npow (n : ℕ) : RingQuot r → RingQuot r
  | ⟨a⟩ =>
    ⟨Quot.lift (fun a ↦ Quot.mk (RingQuot.Rel r) (a ^ n))
        (fun a b (h : Rel r a b) ↦ by
          -- note we can't define a `Rel.pow` as `Rel` isn't reflexive so `Rel r 1 1` isn't true
          dsimp only
          induction n with
          | zero => rw [pow_zero, pow_zero]
          | succ n ih =>
            rw [pow_succ, pow_succ]
            -- Porting note:
            -- `simpa [mul_def] using congr_arg₂ (fun x y ↦ mul r ⟨x⟩ ⟨y⟩) (Quot.sound h) ih`
            -- mysteriously doesn't work
            have := congr_arg₂ (fun x y ↦ mul r ⟨x⟩ ⟨y⟩) ih (Quot.sound h)
            dsimp only at this
            simp? [mul_def] at this says simp only [mul_def, Quot.map₂_mk, mk.injEq] at this
            exact this)
        a⟩

-- note: this cannot be irreducible, as otherwise diamonds don't commute.
private def smul [Algebra S R] (n : S) : RingQuot r → RingQuot r
  | ⟨a⟩ => ⟨Quot.map (fun a ↦ n • a) (Rel.smul n) a⟩

instance : NatCast (RingQuot r) :=
  ⟨natCast r⟩

instance : Zero (RingQuot r) :=
  ⟨zero r⟩

instance : One (RingQuot r) :=
  ⟨one r⟩

instance : Add (RingQuot r) :=
  ⟨add r⟩

instance : Mul (RingQuot r) :=
  ⟨mul r⟩

instance : NatPow (RingQuot r) :=
  ⟨fun x n ↦ npow r n x⟩

instance {R : Type uR} [Ring R] (r : R → R → Prop) : Neg (RingQuot r) :=
  ⟨neg r⟩

instance {R : Type uR} [Ring R] (r : R → R → Prop) : Sub (RingQuot r) :=
  ⟨sub r⟩

instance [Algebra S R] : SMul S (RingQuot r) :=
  ⟨smul r⟩

theorem zero_quot : (⟨Quot.mk _ 0⟩ : RingQuot r) = 0 :=
  show _ = zero r by rw [zero_def]

theorem one_quot : (⟨Quot.mk _ 1⟩ : RingQuot r) = 1 :=
  show _ = one r by rw [one_def]

theorem add_quot {a b} : (⟨Quot.mk _ a⟩ + ⟨Quot.mk _ b⟩ : RingQuot r) = ⟨Quot.mk _ (a + b)⟩ := by
  show add r _ _ = _
  rw [add_def]
  rfl

theorem mul_quot {a b} : (⟨Quot.mk _ a⟩ * ⟨Quot.mk _ b⟩ : RingQuot r) = ⟨Quot.mk _ (a * b)⟩ := by
  show mul r _ _ = _
  rw [mul_def]
  rfl

theorem pow_quot {a} {n : ℕ} : (⟨Quot.mk _ a⟩ ^ n : RingQuot r) = ⟨Quot.mk _ (a ^ n)⟩ := by
  show npow r _ _ = _
  rw [npow_def]

theorem neg_quot {R : Type uR} [Ring R] (r : R → R → Prop) {a} :
    (-⟨Quot.mk _ a⟩ : RingQuot r) = ⟨Quot.mk _ (-a)⟩ := by
  show neg r _ = _
  rw [neg_def]
  rfl

theorem sub_quot {R : Type uR} [Ring R] (r : R → R → Prop) {a b} :
    (⟨Quot.mk _ a⟩ - ⟨Quot.mk _ b⟩ : RingQuot r) = ⟨Quot.mk _ (a - b)⟩ := by
  show sub r _ _ = _
  rw [sub_def]
  rfl

theorem smul_quot [Algebra S R] {n : S} {a : R} :
    (n • ⟨Quot.mk _ a⟩ : RingQuot r) = ⟨Quot.mk _ (n • a)⟩ := by
  show smul r _ _ = _
  rw [smul]
  rfl

instance instIsScalarTower [CommSemiring T] [SMul S T] [Algebra S R] [Algebra T R]
    [IsScalarTower S T R] : IsScalarTower S T (RingQuot r) :=
  ⟨fun s t ⟨a⟩ => Quot.inductionOn a fun a' => by simp only [RingQuot.smul_quot, smul_assoc]⟩

instance instSMulCommClass [CommSemiring T] [Algebra S R] [Algebra T R] [SMulCommClass S T R] :
    SMulCommClass S T (RingQuot r) :=
  ⟨fun s t ⟨a⟩ => Quot.inductionOn a fun a' => by simp only [RingQuot.smul_quot, smul_comm]⟩

instance instAddCommMonoid (r : R → R → Prop) : AddCommMonoid (RingQuot r) where
  add := (· + ·)
  zero := 0
  add_assoc := by
    rintro ⟨⟨⟩⟩ ⟨⟨⟩⟩ ⟨⟨⟩⟩
    simp only [add_quot, add_assoc]
  zero_add := by
    rintro ⟨⟨⟩⟩
    simp [add_quot, ← zero_quot, zero_add]
  add_zero := by
    rintro ⟨⟨⟩⟩
    simp only [add_quot, ← zero_quot, add_zero]
  add_comm := by
    rintro ⟨⟨⟩⟩ ⟨⟨⟩⟩
    simp only [add_quot, add_comm]
  nsmul := (· • ·)
  nsmul_zero := by
    rintro ⟨⟨⟩⟩
    simp only [smul_quot, zero_smul, zero_quot]
  nsmul_succ := by
    rintro n ⟨⟨⟩⟩
    simp only [smul_quot, nsmul_eq_mul, Nat.cast_add, Nat.cast_one, add_mul, one_mul,
               add_comm, add_quot]

instance instMonoidWithZero (r : R → R → Prop) : MonoidWithZero (RingQuot r) where
  mul_assoc := by
    rintro ⟨⟨⟩⟩ ⟨⟨⟩⟩ ⟨⟨⟩⟩
    simp only [mul_quot, mul_assoc]
  one_mul := by
    rintro ⟨⟨⟩⟩
    simp only [mul_quot, ← one_quot, one_mul]
  mul_one := by
    rintro ⟨⟨⟩⟩
    simp only [mul_quot, ← one_quot, mul_one]
  zero_mul := by
    rintro ⟨⟨⟩⟩
    simp only [mul_quot, ← zero_quot, zero_mul]
  mul_zero := by
    rintro ⟨⟨⟩⟩
    simp only [mul_quot, ← zero_quot, mul_zero]
  npow n x := x ^ n
  npow_zero := by
    rintro ⟨⟨⟩⟩
    simp only [pow_quot, ← one_quot, pow_zero]
  npow_succ := by
    rintro n ⟨⟨⟩⟩
    simp only [pow_quot, mul_quot, pow_succ]

instance instSemiring (r : R → R → Prop) : Semiring (RingQuot r) where
  natCast := natCast r
  natCast_zero := by simp [Nat.cast, natCast, ← zero_quot]
  natCast_succ := by simp [Nat.cast, natCast, ← one_quot, add_quot]
  left_distrib := by
    rintro ⟨⟨⟩⟩ ⟨⟨⟩⟩ ⟨⟨⟩⟩
    simp only [mul_quot, add_quot, left_distrib]
  right_distrib := by
    rintro ⟨⟨⟩⟩ ⟨⟨⟩⟩ ⟨⟨⟩⟩
    simp only [mul_quot, add_quot, right_distrib]
  nsmul := (· • ·)
  nsmul_zero := by
    rintro ⟨⟨⟩⟩
    simp only [smul_quot, zero_smul, zero_quot]
  nsmul_succ := by
    rintro n ⟨⟨⟩⟩
    simp only [smul_quot, nsmul_eq_mul, Nat.cast_add, Nat.cast_one, add_mul, one_mul,
               add_comm, add_quot]
  __ := instAddCommMonoid r
  __ := instMonoidWithZero r

-- can't be irreducible, causes diamonds in ℤ-algebras
private def intCast {R : Type uR} [Ring R] (r : R → R → Prop) (z : ℤ) : RingQuot r :=
  ⟨Quot.mk _ z⟩

instance instRing {R : Type uR} [Ring R] (r : R → R → Prop) : Ring (RingQuot r) :=
  { RingQuot.instSemiring r with
    neg := Neg.neg
    add_left_neg := by
      rintro ⟨⟨⟩⟩
      simp [neg_quot, add_quot, ← zero_quot]
    sub := Sub.sub
    sub_eq_add_neg := by
      rintro ⟨⟨⟩⟩ ⟨⟨⟩⟩
      simp [neg_quot, sub_quot, add_quot, sub_eq_add_neg]
    zsmul := (· • ·)
    zsmul_zero' := by
      rintro ⟨⟨⟩⟩
      simp [smul_quot, ← zero_quot]
    zsmul_succ' := by
      rintro n ⟨⟨⟩⟩
      simp [smul_quot, add_quot, add_mul, add_comm]
    zsmul_neg' := by
      rintro n ⟨⟨⟩⟩
      simp [smul_quot, neg_quot, add_mul]
    intCast := intCast r
    intCast_ofNat := fun n => congrArg RingQuot.mk <| by
      exact congrArg (Quot.mk _) (Int.cast_natCast _)
    intCast_negSucc := fun n => congrArg RingQuot.mk <| by
      simp_rw [neg_def]
      exact congrArg (Quot.mk _) (Int.cast_negSucc n) }

instance instCommSemiring {R : Type uR} [CommSemiring R] (r : R → R → Prop) :
  CommSemiring (RingQuot r) :=
  { RingQuot.instSemiring r with
    mul_comm := by
      rintro ⟨⟨⟩⟩ ⟨⟨⟩⟩
      simp [mul_quot, mul_comm] }

instance {R : Type uR} [CommRing R] (r : R → R → Prop) : CommRing (RingQuot r) :=
  { RingQuot.instCommSemiring r, RingQuot.instRing r with }

instance instInhabited (r : R → R → Prop) : Inhabited (RingQuot r) :=
  ⟨0⟩

instance instAlgebra [Algebra S R] (r : R → R → Prop) : Algebra S (RingQuot r) where
  smul := (· • ·)
  toFun r := ⟨Quot.mk _ (algebraMap S R r)⟩
  map_one' := by simp [← one_quot]
  map_mul' := by simp [mul_quot]
  map_zero' := by simp [← zero_quot]
  map_add' := by simp [add_quot]
  commutes' r := by
    rintro ⟨⟨a⟩⟩
    simp [Algebra.commutes, mul_quot]
  smul_def' r := by
    rintro ⟨⟨a⟩⟩
    simp [smul_quot, Algebra.smul_def, mul_quot]

/-- The quotient map from a ring to its quotient, as a homomorphism of rings.
-/
irreducible_def mkRingHom (r : R → R → Prop) : R →+* RingQuot r :=
  { toFun := fun x ↦ ⟨Quot.mk _ x⟩
    map_one' := by simp [← one_quot]
    map_mul' := by simp [mul_quot]
    map_zero' := by simp [← zero_quot]
    map_add' := by simp [add_quot] }

theorem mkRingHom_rel {r : R → R → Prop} {x y : R} (w : r x y) : mkRingHom r x = mkRingHom r y := by
  simp [mkRingHom_def, Quot.sound (Rel.of w)]

theorem mkRingHom_surjective (r : R → R → Prop) : Function.Surjective (mkRingHom r) := by
  simp only [mkRingHom_def, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
  rintro ⟨⟨⟩⟩
  simp

@[ext 1100]
theorem ringQuot_ext [Semiring T] {r : R → R → Prop} (f g : RingQuot r →+* T)
    (w : f.comp (mkRingHom r) = g.comp (mkRingHom r)) : f = g := by
  ext x
  rcases mkRingHom_surjective r x with ⟨x, rfl⟩
  exact (RingHom.congr_fun w x : _)

variable [Semiring T]

irreducible_def preLift {r : R → R → Prop} {f : R →+* T} (h : ∀ ⦃x y⦄, r x y → f x = f y) :
  RingQuot r →+* T :=
  { toFun := fun x ↦ Quot.lift f
        (by
          rintro _ _ r
          induction r with
          | of r => exact h r
          | add_left _ r' => rw [map_add, map_add, r']
          | mul_left _ r' => rw [map_mul, map_mul, r']
          | mul_right _ r' => rw [map_mul, map_mul, r'])
        x.toQuot
    map_zero' := by simp only [← zero_quot, f.map_zero]
    map_add' := by
      rintro ⟨⟨x⟩⟩ ⟨⟨y⟩⟩
      simp only [add_quot, f.map_add x y]
    map_one' := by simp only [← one_quot, f.map_one]
    map_mul' := by
      rintro ⟨⟨x⟩⟩ ⟨⟨y⟩⟩
      simp only [mul_quot, f.map_mul x y] }

/-- Any ring homomorphism `f : R →+* T` which respects a relation `r : R → R → Prop`
factors uniquely through a morphism `RingQuot r →+* T`.
-/
irreducible_def lift {r : R → R → Prop} :
  { f : R →+* T // ∀ ⦃x y⦄, r x y → f x = f y } ≃ (RingQuot r →+* T) :=
  { toFun := fun f ↦ preLift f.prop
    invFun := fun F ↦ ⟨F.comp (mkRingHom r), fun x y h ↦ congr_arg F (mkRingHom_rel h)⟩
    left_inv := fun f ↦ by
      ext
      simp only [preLift_def, mkRingHom_def, RingHom.coe_comp, RingHom.coe_mk, MonoidHom.coe_mk,
                 OneHom.coe_mk, Function.comp_apply]
    right_inv := fun F ↦ by
      simp only [preLift_def]
      ext
      simp only [mkRingHom_def, RingHom.coe_comp, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
                 Function.comp_apply, forall_const] }

@[simp]
theorem lift_mkRingHom_apply (f : R →+* T) {r : R → R → Prop} (w : ∀ ⦃x y⦄, r x y → f x = f y) (x) :
    lift ⟨f, w⟩ (mkRingHom r x) = f x := by
  simp_rw [lift_def, preLift_def, mkRingHom_def]
  rfl

-- note this is essentially `lift.symm_apply_eq.mp h`
theorem lift_unique (f : R →+* T) {r : R → R → Prop} (w : ∀ ⦃x y⦄, r x y → f x = f y)
    (g : RingQuot r →+* T) (h : g.comp (mkRingHom r) = f) : g = lift ⟨f, w⟩ := by
  ext
  simp [h]

theorem eq_lift_comp_mkRingHom {r : R → R → Prop} (f : RingQuot r →+* T) :
    f = lift ⟨f.comp (mkRingHom r), fun x y h ↦ congr_arg f (mkRingHom_rel h)⟩ := by
  conv_lhs => rw [← lift.apply_symm_apply f]
  rw [lift_def]
  rfl

section CommRing

/-!
We now verify that in the case of a commutative ring, the `RingQuot` construction
agrees with the quotient by the appropriate ideal.
-/


variable {B : Type uR} [CommRing B]

/-- The universal ring homomorphism from `RingQuot r` to `B ⧸ Ideal.ofRel r`. -/
def ringQuotToIdealQuotient (r : B → B → Prop) : RingQuot r →+* B ⧸ Ideal.ofRel r :=
  lift ⟨Ideal.Quotient.mk (Ideal.ofRel r),
        fun x y h ↦ Ideal.Quotient.eq.2 <| Submodule.mem_sInf.mpr
          fun _ w ↦ w ⟨x, y, h, sub_add_cancel x y⟩⟩

@[simp]
theorem ringQuotToIdealQuotient_apply (r : B → B → Prop) (x : B) :
    ringQuotToIdealQuotient r (mkRingHom r x) = Ideal.Quotient.mk (Ideal.ofRel r) x := by
  simp_rw [ringQuotToIdealQuotient, lift_def, preLift_def, mkRingHom_def]
  rfl

/-- The universal ring homomorphism from `B ⧸ Ideal.ofRel r` to `RingQuot r`. -/
def idealQuotientToRingQuot (r : B → B → Prop) : B ⧸ Ideal.ofRel r →+* RingQuot r :=
  Ideal.Quotient.lift (Ideal.ofRel r) (mkRingHom r)
    (by
      refine fun x h ↦ Submodule.span_induction h ?_ ?_ ?_ ?_
      · rintro y ⟨a, b, h, su⟩
        symm at su
        rw [← sub_eq_iff_eq_add] at su
        rw [← su, RingHom.map_sub, mkRingHom_rel h, sub_self]
      · simp
      · intro a b ha hb
        simp [ha, hb]
      · intro a x hx
        simp [hx])

@[simp]
theorem idealQuotientToRingQuot_apply (r : B → B → Prop) (x : B) :
    idealQuotientToRingQuot r (Ideal.Quotient.mk _ x) = mkRingHom r x :=
  rfl


/-- The ring equivalence between `RingQuot r` and `(Ideal.ofRel r).quotient`
-/
def ringQuotEquivIdealQuotient (r : B → B → Prop) : RingQuot r ≃+* B ⧸ Ideal.ofRel r :=
  RingEquiv.ofHomInv (ringQuotToIdealQuotient r) (idealQuotientToRingQuot r)
    (by
      ext x
      simp_rw [ringQuotToIdealQuotient, lift_def, preLift_def, mkRingHom_def]
      change mkRingHom r x = _
      rw [mkRingHom_def]
      rfl)
    (by
      ext x
      simp_rw [ringQuotToIdealQuotient, lift_def, preLift_def, mkRingHom_def]
      change Quot.lift _ _ ((mkRingHom r) x).toQuot = _
      rw [mkRingHom_def]
      rfl)

end CommRing

section Algebra

variable (S)

/-- The quotient map from an `S`-algebra to its quotient, as a homomorphism of `S`-algebras.
-/
irreducible_def mkAlgHom (s : A → A → Prop) : A →ₐ[S] RingQuot s :=
  { mkRingHom s with
    commutes' := fun _ ↦ by simp [mkRingHom_def]; rfl }

@[simp]
theorem mkAlgHom_coe (s : A → A → Prop) : (mkAlgHom S s : A →+* RingQuot s) = mkRingHom s := by
  simp_rw [mkAlgHom_def, mkRingHom_def]
  rfl

theorem mkAlgHom_rel {s : A → A → Prop} {x y : A} (w : s x y) :
    mkAlgHom S s x = mkAlgHom S s y := by
  simp [mkAlgHom_def, mkRingHom_def, Quot.sound (Rel.of w)]

theorem mkAlgHom_surjective (s : A → A → Prop) : Function.Surjective (mkAlgHom S s) := by
  suffices Function.Surjective fun x ↦ (⟨.mk (Rel s) x⟩ : RingQuot s) by
    simpa [mkAlgHom_def, mkRingHom_def]
  rintro ⟨⟨a⟩⟩
  use a

variable {B : Type u₄} [Semiring B] [Algebra S B]

@[ext 1100]
theorem ringQuot_ext' {s : A → A → Prop} (f g : RingQuot s →ₐ[S] B)
    (w : f.comp (mkAlgHom S s) = g.comp (mkAlgHom S s)) : f = g := by
  ext x
  rcases mkAlgHom_surjective S s x with ⟨x, rfl⟩
  exact AlgHom.congr_fun w x

irreducible_def preLiftAlgHom {s : A → A → Prop} {f : A →ₐ[S] B}
  (h : ∀ ⦃x y⦄, s x y → f x = f y) : RingQuot s →ₐ[S] B :=
{ toFun := fun x ↦ Quot.lift f
            (by
              rintro _ _ r
              induction r with
              | of r => exact h r
              | add_left _ r' => simp only [map_add, r']
              | mul_left _ r' => simp only [map_mul, r']
              | mul_right _ r' => simp only [map_mul, r'])
            x.toQuot
  map_zero' := by simp only [← zero_quot, map_zero]
  map_add' := by
    rintro ⟨⟨x⟩⟩ ⟨⟨y⟩⟩
    simp only [add_quot, map_add _ x y]
  map_one' := by simp only [← one_quot, map_one]
  map_mul' := by
    rintro ⟨⟨x⟩⟩ ⟨⟨y⟩⟩
    simp only [mul_quot, map_mul _ x y]
  commutes' := by
    rintro x
    simp [← one_quot, smul_quot, Algebra.algebraMap_eq_smul_one] }

/-- Any `S`-algebra homomorphism `f : A →ₐ[S] B` which respects a relation `s : A → A → Prop`
factors uniquely through a morphism `RingQuot s →ₐ[S] B`.
-/
irreducible_def liftAlgHom {s : A → A → Prop} :
  { f : A →ₐ[S] B // ∀ ⦃x y⦄, s x y → f x = f y } ≃ (RingQuot s →ₐ[S] B) :=
  { toFun := fun f' ↦ preLiftAlgHom _ f'.prop
    invFun := fun F ↦ ⟨F.comp (mkAlgHom S s), fun _ _ h ↦ congr_arg F (mkAlgHom_rel S h)⟩
    left_inv := fun f ↦ by
      ext
      simp only [preLiftAlgHom_def, mkAlgHom_def, mkRingHom_def, RingHom.toMonoidHom_eq_coe,
                 RingHom.coe_monoidHom_mk, AlgHom.coe_comp, AlgHom.coe_mk, RingHom.coe_mk,
                 MonoidHom.coe_mk, OneHom.coe_mk, Function.comp_apply]
    right_inv := fun F ↦ by
      ext
      simp only [preLiftAlgHom_def, mkAlgHom_def, mkRingHom_def, RingHom.toMonoidHom_eq_coe,
                 RingHom.coe_monoidHom_mk, AlgHom.coe_comp, AlgHom.coe_mk, RingHom.coe_mk,
                 MonoidHom.coe_mk, OneHom.coe_mk, Function.comp_apply] }

@[simp]
theorem liftAlgHom_mkAlgHom_apply (f : A →ₐ[S] B) {s : A → A → Prop}
    (w : ∀ ⦃x y⦄, s x y → f x = f y) (x) : (liftAlgHom S ⟨f, w⟩) ((mkAlgHom S s) x) = f x := by
  simp_rw [liftAlgHom_def, preLiftAlgHom_def, mkAlgHom_def, mkRingHom_def]
  rfl

-- note this is essentially `(liftAlgHom S).symm_apply_eq.mp h`
theorem liftAlgHom_unique (f : A →ₐ[S] B) {s : A → A → Prop} (w : ∀ ⦃x y⦄, s x y → f x = f y)
    (g : RingQuot s →ₐ[S] B) (h : g.comp (mkAlgHom S s) = f) : g = liftAlgHom S ⟨f, w⟩ := by
  ext
  simp [h]

theorem eq_liftAlgHom_comp_mkAlgHom {s : A → A → Prop} (f : RingQuot s →ₐ[S] B) :
    f = liftAlgHom S ⟨f.comp (mkAlgHom S s), fun x y h ↦ congr_arg f (mkAlgHom_rel S h)⟩ := by
  conv_lhs => rw [← (liftAlgHom S).apply_symm_apply f]
  rw [liftAlgHom]
  rfl

end Algebra

end RingQuot
