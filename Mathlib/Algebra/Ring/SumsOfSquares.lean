/-
Copyright (c) 2024 Florent Schaffhauser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florent Schaffhauser, Artie Khovanov
-/
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Group.Submonoid.Basic
import Mathlib.Algebra.Group.Even
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Ring.Subsemiring.Basic

/-!
# Sums of squares

We introduce sums of squares in a type `R` endowed with an `[Add R]`, `[Zero R]` and `[Mul R]`
instances. Sums of squares in `R` are defined by an inductive predicate `IsSumSq : R → Prop`:
`0 : R` is a sum of squares and if `S` is a sum of squares, then for all `a : R`, `a * a + S` is a
sum of squares in `R`.

## Main declaration

- The predicate `IsSumSq : R → Prop`, defining the property of being a sum of squares in `R`.

## Auxiliary declarations

- The terms `AddMonoid.sumSqIn R` and `Subsemiring.sumSqIn R` :
in an additive monoid with multiplication `R` and a semiring `R`, we introduce the terms
`AddMonoid.sumSqIn R` and `Subsemiring.sumSqIn R` as the submonoid and subsemiring, respectively,
of `R` whose carrier is the subset `{S : R | IsSumSq S}`.

## Theorems

- `IsSumSq.add`: if `S1` and `S2` are sums of squares in `R`, then so is `S1 + S2`.
- `IsSumSq.mul`: if `S1` and `S2` are sums of squares in `R`, then so is `S1 * S2`.
- `isSumSq_isSquare`: a square in `R` is a sum of squares in `R`.
- `IsSumSq.nonneg`: sums of squares are non-negative.
- `AddSubmonoid.closure_isSquare`: the submonoid of `R` generated by the squares in `R` is the set
of sums of squares in `R`.
- `Subsemiring.closure_isSquare`: the subsemiring of `R` generated by the squares in `R` is the set
of sums of squares in `R`.

-/

variable {R : Type*}

/--
In a type `R` with an addition, a zero element and a multiplication, the property of being a sum of
squares is defined by an inductive predicate: `0 : R` is a sum of squares and if `S` is a sum of
squares, then for all `a : R`, `a * a + S` is a sum of squares in `R`.
-/
@[mk_iff]
inductive IsSumSq [Mul R] [Add R] [Zero R] : R → Prop
  | zero                              : IsSumSq 0
  | sq_add (a S : R) (hS : IsSumSq S) : IsSumSq (a * a + S)

/-- In an additive monoid with multiplication,
if `S1` and `S2` are sums of squares, then `S1 + S2` is a sum of squares. -/
theorem IsSumSq.add [AddMonoid R] [Mul R] {S1 S2 : R}
    (h1 : IsSumSq S1) (h2 : IsSumSq S2) : IsSumSq (S1 + S2) := by
  induction h1 with
  | zero             => rw [zero_add]; exact h2
  | sq_add a S pS ih => rw [add_assoc]; exact IsSumSq.sq_add a (S + S2) ih

/-- In an additive unital magma with multiplication, `x * x` is a sum of squares for all `x`. -/
theorem isSumSq_mul_self [AddZeroClass R] [Mul R] (a : R) : IsSumSq (a * a) := by
  rw [← add_zero (a * a)]
  exact IsSumSq.sq_add _ _ IsSumSq.zero

/-- In an additive unital magma with multiplication `R`, squares in `R` are sums of squares.
By definition, a square in `R` is a term `x : R` such that `x = y * y` for some `y : R`
and in Mathlib this is known as `IsSquare R` (see Mathlib.Algebra.Group.Even). -/
theorem isSumSq_isSquare [AddZeroClass R] [Mul R] {x : R} (hx : IsSquare x) : IsSumSq x := by
  rcases hx with ⟨a, ha⟩
  rw [ha]
  exact isSumSq_mul_self a

/-- Alternative induction scheme for `IsSumSq` using `IsSquare`. -/
theorem IsSumSq.induction_alt [Mul R] [Add R] [Zero R]
    {p : (S : R) → (h : IsSumSq S) → Prop} (S : R) (hS : IsSumSq S)
    (zero : p 0 zero)
    (sq_add : ∀ x S, (hS : IsSumSq S) → (hx : IsSquare x) → p S hS →
      p (x + S) (by rcases hx with ⟨y, hy⟩; rw [hy]; exact sq_add y S hS)) : p S hS := by
  induction hS with
  | zero => exact zero
  | sq_add a S hS hS_ih => apply sq_add (a * a) S hS _ hS_ih; use a

/-- Helper lemma for `IsSumSq.mul`. -/
private theorem IsSumSq.mul_isSquare [NonUnitalCommSemiring R] {S x : R}
    (hS : IsSumSq S) (hx : IsSquare x) : IsSumSq (S * x) := by
  induction' S, hS using IsSumSq.induction_alt
  case zero => simpa using zero
  case sq_add y T hT hy ih => rw [right_distrib]
                              exact IsSumSq.add (isSumSq_isSquare (IsSquare.mul hy hx)) ih

/-- In a (not necessarily unital) commutative semiring,
if `S1` and `S2` are sums of squares, then `S1 * S2` is a sum of squares. -/
theorem IsSumSq.mul [NonUnitalCommSemiring R] {S1 S2 : R}
    (h1 : IsSumSq S1) (h2 : IsSumSq S2) : IsSumSq (S1 * S2) := by
  induction' S2, h2 using IsSumSq.induction_alt
  case zero => simpa using zero
  case sq_add y T hT hy ih => rw [left_distrib]
                              exact IsSumSq.add (IsSumSq.mul_isSquare h1 hy) ih

namespace AddSubmonoid
variable {T : Type*} [AddMonoid T] [Mul T] {a : T}

variable (T) in
/--
In an additive monoid with multiplication `R`, the type `AddSubmonoid.sumSqIn R`
is the submonoid of sums of squares in `R`.
-/
def sumSqIn : AddSubmonoid T where
  carrier := {S : T | IsSumSq S}
  zero_mem' := IsSumSq.zero
  add_mem' := IsSumSq.add

@[simp] lemma mem_sumSqIn : a ∈ sumSqIn T ↔ IsSumSq a := Iff.rfl
@[simp, norm_cast] lemma coe_sumSqIn : sumSqIn T = {x : T | IsSumSq x} := rfl

end AddSubmonoid

namespace Subsemiring
variable {T : Type*} [CommSemiring T] {a : T}

variable (T) in
/--
In a commutative semiring `R`, the type `Subsemiring.sumSqIn R`
is the subsemiring of sums of squares in `R`.
-/
def sumSqIn : Subsemiring T where
  __ := AddSubmonoid.sumSqIn T
  mul_mem' := IsSumSq.mul
  one_mem' := isSumSq_isSquare isSquare_one

@[simp] lemma sumSqIn_toAddSubmonoid : (sumSqIn T).toAddSubmonoid = .sumSqIn T := rfl
@[simp] lemma mem_sumSqIn : a ∈ sumSqIn T ↔ IsSumSq a := Iff.rfl
@[simp, norm_cast] lemma coe_sumSqIn : sumSqIn T = {x : T | IsSumSq x} := rfl

end Subsemiring

/--
In an additive monoid with multiplication `R`, the submonoid generated by the squares is the set of
sums of squares in `R`.
-/
theorem AddSubmonoid.closure_isSquare [AddMonoid R] [Mul R] :
    closure {x : R | IsSquare x} = sumSqIn R := by
  refine le_antisymm (closure_le.2 (fun x hx ↦ isSumSq_isSquare hx)) (fun x hx ↦ ?_)
  induction hx with
  | zero             => exact zero_mem _
  | sq_add a S _ ih  => exact AddSubmonoid.add_mem _ (subset_closure ⟨a, rfl⟩) ih

/--
In a commutative semiring `R`, the subsemiring generated by the squares is the set of
sums of squares in `R`.
-/
theorem Subsemiring.closure_isSquare [CommSemiring R] :
    closure {x : R | IsSquare x} = sumSqIn R := by
  refine le_antisymm (closure_le.2 (fun x hx ↦ isSumSq_isSquare hx)) (fun x hx ↦ ?_)
  induction hx with
  | zero             => exact zero_mem _
  | sq_add a S _ ih  => exact Subsemiring.add_mem _ (subset_closure ⟨a, rfl⟩) ih

/--
Let `R` be a linearly ordered semiring in which the property `a ≤ b → ∃ c, a + c = b` holds
(e.g. `R = ℕ`). If `S : R` is a sum of squares in `R`, then `0 ≤ S`. This is used in
`Mathlib.Algebra.Ring.Semireal.Defs` to show that such semirings are semireal.
-/
theorem IsSumSq.nonneg {R : Type*} [LinearOrderedSemiring R] [ExistsAddOfLE R] {S : R}
    (pS : IsSumSq S) : 0 ≤ S := by
  induction pS with
  | zero             => simp only [le_refl]
  | sq_add x S _ ih  => apply add_nonneg (mul_self_nonneg x) ih
