/-
Copyright (c) 2024 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.Positivity

/-! # Tests for the module-normalization tactic -/

open Mathlib.Tactic.LinearCombination

variable {V : Type*} {K : Type} -- TODO generalize universes
  {t u v w x y z : V} {a b c d e f μ ν ρ : K}

/-! ### `ℕ` (tests copied from the `abel` tactic) -/

section Nat
variable [AddCommMonoid V]

example : x + (y + x) = x + x + y := by module
example : (3 : ℕ) • x = x + (2 : ℕ) • x := by module
example : x + (y + x) = x + x + y := by module
example : (3 : ℕ) • x = x + (2 : ℕ) • x := by module
example : x + (y + (x + (z + (x + (u + (x + v)))))) = v + u + z + y + 4 • x := by module

-- Make sure we fail on some non-equalities.
example : x + (y + (x + (z + (x + (u + (x + v)))))) = v + u + z + y + 3 • x ∨ True := by
  fail_if_success
    left; module
  right; trivial

end Nat

/-! ### `ℤ` (most tests copied from the `abel` tactic) -/

variable [AddCommGroup V]

example : (x + y) - ((y + x) + x) = -x := by module
example : x - 0 = x := by module
example : (3 : ℤ) • x = x + (2 : ℤ) • x := by module
example : x - 2 • y = x - 2 • y := by module
example : (x + y) - ((y + x) + x) = -x := by module
example : x - 0 = x := by module
example : (3 : ℤ) • x = x + (2 : ℤ) • x := by module
example : x - 2 • y = x - 2 • y := by module
example : 0 + x = x := by module
example (n : ℕ) : n • x = n • x := by module
example (n : ℕ) : 0 + n • x = n • x := by module
example : x + (y + (x + (z + (x + (u + (x + v)))))) = v + u + z + y + 4 • x := by module
example : x + y + (z + w - x) = y + z + w := by module
example : x + y + z + (z - x - x) = (-1) • x + y + 2 • z := by module
example : x + y = y + x := by module
example : x + 2 • x = 2 • x + x := by module
example : -x + x = 0 := by module

-- Make sure we fail on some non-equalities.

example : x + (y + (x + (z + (x + (u + (x + v)))))) = v + u + z + y + 3 • x ∨ True := by
  fail_if_success
    left; module
  right; trivial

example : x + y + (z + w - x) = y + z - w ∨ True := by
  fail_if_success
    left; module
  right; trivial

example : x + y + z + (z - x - x) = (-1) • x + y + z ∨ True := by
  fail_if_success
    left; module
  right; trivial

-- https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/Interaction.20of.20abel.20with.20casting/near/319895001
example : True := by
  have : ∀ (p q r s : V), s + p - q = s - r - (q - r - p) := by
    intro p q r s
    module
  trivial

-- https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/Interaction.20of.20abel.20with.20casting/near/319897374
example : y = x + z - (x - y + z) := by
  have : True := trivial
  module

-- https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/abel.20bug.3F/near/368707560
example : -y + (z - x) = z - y - x := by module

/-! ### Commutative ring -/

section CommRing
variable [CommRing K] [Module K V]

example : a • x + b • x = (a + b) • x := by module
example : a • x - b • x = (a - b) • x := by module
example : a • x - b • y = a • x + (-b) • y := by module
example : 2 • a • x = a • 2 • x := by module

-- from https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/linear_combination.20for.20groups/near/437042918
example : (1 + a ^ 2) • (v + w) - a • (a • v - w) = v + (1 + a + a ^ 2) • w := by module

example (h : a = b) : a • x = b • x := by
  match_scalars
  linear_combination h

example (h : a = b) : a • x = b • x := by
  -- `linear_combination h • x`
  apply eq_of_add (congr($h • x):)
  module

example (h : a ^ 2 + b ^ 2 = 1) : a • (a • x - b • y) + (b • a • y + b • b • x) = x := by
  match_scalars
  · linear_combination h
  · ring

example (h : a ^ 2 + b ^ 2 = 1) : a • (a • x - b • y) + (b • a • y + b • b • x) = x := by
  -- `linear_combination h • x`
  apply eq_of_add (congr($h • x):)
  module

-- from https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/smul.20diamond/near/457163013
example : (4 : ℤ) • v = (4 : K) • v := by module
example : (4 : ℕ) • v = (4 : K) • v := by module

example : (μ - ν) • a • x = (a • μ • x + b • ν • y) - ν • (a • x + b • y) := by module

example : (μ - ν) • b • y = μ • (a • x + b • y) - (a • μ • x + b • ν • y) := by module

example (h1 : a • x + b • y = 0) (h2 : a • μ • x + b • ν • y = 0) : (μ - ν) • a • x = 0 := by
  -- `linear_combination h2 - ν • h1`
  apply eq_of_add (congr($h2 - ν • $h1):)
  module

example (h1 : 0 • z + a • x + b • y = 0) (h2 : 0 • ρ • z + a • μ • x + b • ν • y = 0) :
    (μ - ν) • a • x = 0 := by
  -- `linear_combination h2 - ν • h1`
  apply eq_of_add (congr($h2 - ν • $h1):)
  module

example (h1 : a • x + b • y = 0) (h2 : a • μ • x + b • ν • y = 0) :
    (μ - ν) • b • y = 0 := by
  -- `linear_combination μ • h1 + h2`
  apply eq_of_add (congr(μ • $h1 - $h2):)
  module

example
    (h1 : a • x + b • y + c • z = 0)
    (h2 : a • μ • x + b • ν • y + c • ρ • z = 0)
    (h3 : a • μ • μ • x + b • ν • ν • y + c • ρ • ρ • z = 0) :
    (μ - ν) • (μ - ρ) • a • x = 0 := by
  apply eq_of_add (congr($h3 - (ν + ρ) • $h2 + ν • ρ • $h1):)
  module

example
    (h1 : a • x + b • y + c • z = 0)
    (h2 : a • μ • x + b • ν • y + c • ρ • z = 0)
    (h3 : a • μ • μ • x + b • ν • ν • y + c • ρ • ρ • z = 0) :
    (μ - ν) • (ν - ρ) • b • y = 0 := by
  apply eq_of_add (congr(- $h3 + (μ + ρ) • $h2 - μ • ρ • $h1):)
  module

example
    (h1 : a • x + b • y + c • z = 0)
    (h2 : a • μ • x + b • ν • y + c • ρ • z = 0)
    (h3 : a • μ • μ • x + b • ν • ν • y + c • ρ • ρ • z = 0) :
    (μ - ρ) • (ν - ρ) • c • z = 0 := by
  apply eq_of_add (congr($h3 - (μ + ν) • $h2 + μ • ν • $h1):)
  module

/--
error: unsolved goals
V : Type u_1
K : Type
t u v w x y z : V
a b c d e f μ ν ρ : K
inst✝² : AddCommGroup V
inst✝¹ : CommRing K
inst✝ : Module K V
⊢ 2 * (a * 1) = 2
-/
#guard_msgs in
example : 2 • a • x = 2 • x := by module

end CommRing

/-! ### Characteristic-zero field -/

section CharZeroField
variable [Field K] [CharZero K] [Module K V]

example : (2:K)⁻¹ • x + (3:K)⁻¹ • x + (6:K)⁻¹ • x = x := by module

example (h₁ : t - u = -(v - w)) (h₂ : t + u = v + w) : t = w := by
  -- `linear_combination 2⁻¹ • h₁ + 2⁻¹ • h₂`
  apply eq_of_add (congr((2:K)⁻¹ • $h₁ + (2:K)⁻¹ • $h₂):)
  module

end CharZeroField

/-! ### Linearly ordered field -/

section LinearOrderedField
variable [LinearOrderedField K] [Module K V]

example (ha : 0 ≤ a) (hb : 0 < b) :
    x = (a / (a + b)) • y + (b / (a + b)) • (x + (a / b) • (x - y)) := by
  match_scalars
  · field_simp
    ring
  · field_simp
    ring

-- From Analysis.Convex.StoneSeparation
example (hab : 0 < a * b + c * d) :
    (a * b / (a * b + c * d) * e) • u + (c * d / (a * b + c * d) * f) • v +
      ((a * b / (a * b + c * d)) • d • x + (c * d / (a * b + c * d)) • b • y) =
      (a * b + c * d)⁻¹ • ((a * b * e) • u + ((c * d * f) • v +
        ((a * b) • d • x + (c * d) • b • y))) := by
  match_scalars
  · field_simp
  · field_simp
  · field_simp
  · field_simp

example (h₁ : 1 = a ^ 2 + b ^ 2) (h₂ : 1 - a ≠ 0) :
    ((2 / (1 - a)) ^ 2 * b ^ 2 + 4)⁻¹ • (4:K) • ((2 / (1 - a)) • y)
    + ((2 / (1 - a)) ^ 2 * b ^ 2 + 4)⁻¹ • ((2 / (1 - a)) ^ 2 * b ^ 2 - 4) • x
    = a • x + y := by
  -- `linear_combination (h₁ * (b ^ 2 + (1 - a) ^ 2)⁻¹) • (y + (a - 1) • x)`
  apply eq_of_add (congr(($h₁ * (b ^ 2 + (1 - a) ^ 2)⁻¹) • (y + (a - 1) • x)):)
  match_scalars
  · field_simp
    ring
  · field_simp
    ring

example (h₁ : 1 = a ^ 2 + b ^ 2) (h₂ : 1 - a ≠ 0) :
    ((2 / (1 - a)) ^ 2 * b ^ 2 + 4)⁻¹ • (4:K) • ((2 / (1 - a)) • y)
    + ((2 / (1 - a)) ^ 2 * b ^ 2 + 4)⁻¹ • ((2 / (1 - a)) ^ 2 * b ^ 2 - 4) • x
    = a • x + y := by
  match_scalars
  · field_simp
    linear_combination 4 * (1 - a) * h₁
  · field_simp
    linear_combination 4 * (a - 1) ^ 3 * h₁

end LinearOrderedField
