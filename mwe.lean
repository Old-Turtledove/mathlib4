import Mathlib

/-!
# application type mismatch

This is a very common error for beginners who tend to make a bunch of arguments explicit in some
`variable` statement.
-/

section application_type_mismatch

/-! The following line accidentally makes `G` be explicit in `fancy`. -/
variable (G : Type) [AddCommGroup G]

/-! If your variable statement is very high up in the file, it might look like `fancyOp` takes two
explicit arguments only: `a` and `b`. -/
def fancyOp (a b : G) : G := a + b - b

/-! Lean complains that you are providing `a` instead of `G`. -/
lemma fancyOp_eq_left (a b : G) : fancyOp a b = a := sorry

end application_type_mismatch























section no_application_type_mismatch

/-! The better way to deal with this is to avoid declaring *any* explicit argument in the
`variable`. This is obviously a rule of thumb which you should feel free to disregard when there is
a good reason to do so. -/
variable {G : Type} [AddCommGroup G]

def otherFancyOp (a b : G) : G := a + b - b

/-! Works as expected. -/
lemma otherFancyOp_eq_left (a b : G) : otherFancyOp a b = a := sorry

end no_application_type_mismatch














/-!
# don't know how to synthesize placeholder

This is kind of the dual error to the above, as it often happens when too many arguments to a
definition are implicit. too many -/

section dont_know_how_to_synthesize_placeholder

def mulByZero {𝕜 E : Type} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E] (x : E) : E := (0 : 𝕜) • x

lemma mulByZero_eq_zero {𝕜 E : Type} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E] (x : E) :
    mulByZero x = 0 := sorry

end dont_know_how_to_synthesize_placeholder





section dont_know_how_to_synthesize_placeholder

def mulByZero' {𝕜 E : Type} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E] (x : E) : E := (0 : 𝕜) • x

lemma mulByZero'_eq_zero {E : Type} [AddCommGroup E] [Module ℂ E] (x : E) :
    mulByZero' (𝕜 := ℂ) x = 0 := sorry

end dont_know_how_to_synthesize_placeholder





section dont_know_how_to_synthesize_placeholder

variable {𝕜 E : Type} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E]

-- a lot of junk here

#where

/-! Binder update -/
variable (𝕜) in
def mulByZero'' (x : E) : E := (0 : 𝕜) • x

#where

lemma mulByZero''_eq_zero (x : E) : mulByZero'' (𝕜 := ℂ) x = 0 := sorry

end dont_know_how_to_synthesize_placeholder





















section Noncomputable

noncomputable def twoOverThree : ℝ := 2 / 3

def twoOverThree' : ℝ := (2 / 3 : ℚ)

/-!
# compiler IR error failed
-/

end Noncomputable

























/-! # failed to synthesize instance -/

section failed_to_synthesize_instance

variable {ι : Type} [Fintype ι] [DecidableEq ι]

lemma card_eq_card_ι_sub_one (i : ι) : Fintype.card {j // j ≠ i} = Fintype.card ι - 1 := sorry

end failed_to_synthesize_instance























lemma balh {G : Type*} [Group G] {N : Subgroup G} [N.Normal] [@Std.Commutative (G ⧸ N) (· * ·)]
    (a b : G ⧸ N) :
    a * b = b * a := by
  let ete : CommGroup (G ⧸ N) :=
    { (inferInstance :  Group (G ⧸ N) ) with
      mul_comm := Std.Commutative.comm }
  sorry -- good here


lemma weird [Ring ℝ] : Real.pi + Real.exp 1 = Real.exp 1 + Real.pi := sorry
