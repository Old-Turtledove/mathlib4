/-
Copyright (c) 2023 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
import Mathlib.Data.MvPolynomial.Equiv
import Mathlib.Data.Polynomial.RingDivision
import Mathlib.Data.Fin.Tuple.Basic

/-!
# The Schwartz-Zippel lemma

This file contains a proof of the
[Schwartz-Zippel](https://en.wikipedia.org/wiki/Schwartz%E2%80%93Zippel_lemma) lemma.
This lemma tells us that the probability that a nonzero multivariable polynomial over a integral domain evaluates to zero at a random point is bounded by the degree of the polynomial over the size of the field, or more generally, that a nonzero multivariable polynomial over any integral domain has a low probability of being zero when evaluated at points drawn at random from some finite subset of the field. This lemma is useful as a probabilistic polynomial identity test.

## TODO

* Generalize to subset of the ring being different for each variable
* Reexpress in terms of probabilities.
* Write a tactic to apply this lemma to a given polynomial

-/

open BigOperators

section find_home


-- REVIEWERS: Not sure what to do here.
-- Presumably we don't want these lemmas, but the proof below is more complicated without them
lemma and_or_and_not_iff (p q : Prop) : ((p ∧ q) ∨ (p ∧ ¬ q)) ↔ p := by
  tauto

lemma and_and_and_not_iff (p q : Prop) : ((p ∧ q) ∧ (p ∧ ¬ q)) ↔ false := by
  tauto

@[simp]
lemma MvPolynomial.support_nonempty_iff {F σ} [CommSemiring F] (p : MvPolynomial σ F) :
    (MvPolynomial.support p).Nonempty ↔ p ≠ 0 := by
  rw [ne_eq, ←MvPolynomial.support_eq_empty, Finset.nonempty_iff_ne_empty]

-- https://github.com/leanprover-community/mathlib4/pull/7898
lemma Finset.card_filter_piFinset_eq' {n : ℕ} {α : Fin (n + 1) → Type*}
    (p : ((i : Fin n) → α i.succ) → Prop) [DecidablePred p]
    (S : (i : Fin (n + 1)) → Finset (α i)) :
    Finset.card (Finset.filter (fun r ↦ p (fun x ↦ r $ Fin.succ x)) (Fintype.piFinset S))
      = Finset.card ((S 0) ×ˢ Finset.filter p (Fintype.piFinset (fun x ↦ S $ Fin.succ x))) := by
  rw [←Finset.card_map ((Equiv.piFinSuccAboveEquiv α 0).toEmbedding)]
  congr
  ext ⟨x, f⟩
  simp? [Fin.forall_fin_succ] says simp only [Fin.zero_succAbove, Fintype.mem_piFinset,
      Fin.forall_fin_succ, and_imp, mem_map_equiv, mem_filter, mem_product]
  tauto

-- https://github.com/leanprover-community/mathlib4/pull/7898
@[simp]
lemma Finset.card_filter_succ_piFinset_eq {n : ℕ} {α : Fin (n + 1) → Type*}
    (p : ((i : Fin n) → α i.succ) → Prop) [DecidablePred p]
    (S : (i : Fin (n + 1)) → Finset (α i)) :
    Finset.card (Finset.filter (fun r ↦ p (fun x ↦ r $ Fin.succ x)) (Fintype.piFinset S))
     = (S 0).card * Finset.card (Finset.filter p (Fintype.piFinset (fun x ↦ S $ Fin.succ x))) := by
  rw [card_filter_piFinset_eq']
  exact Finset.card_product (S 0) (Finset.filter p (Fintype.piFinset (fun x ↦ S $ Fin.succ x)))




lemma AlgEquiv_invFun_apply {R α β : Type} [CommSemiring R] [Semiring α] [Semiring β] [Algebra R α] [Algebra R β]
    (e : α ≃ₐ[R] β) (x : α) : x = (e).symm ((e) x) := by
  simp only [AlgEquiv.symm_apply_apply]
  -- rw [AlgEquiv.toEquiv_eq_coe, Equiv.invFun_as_coe, @Equiv.eq_symm_apply]
  -- exact rfl


end find_home



/--
The **Schwartz-Zippel lemma**: For a nonzero multivariable polynomial `p` over a integral domain, the
probability that `p` evaluates to zero at points drawn at random from some finite subset `S` of the
integral domain is bounded by the degree of `p` over `|S|`. This version presents this lemma in terms of
-/
lemma schwartz_zippel (F : Type) [CommRing F] [IsDomain F] [DecidableEq F] (n : ℕ)
    (p : MvPolynomial (Fin n) F) (hp : p ≠ 0) (S : Finset F) :
    (Finset.filter
      (fun f => MvPolynomial.eval f p = 0)
      (Fintype.piFinset (fun _ => S))).card * S.card
      ≤ (p.totalDegree) * S.card ^ n := by
  -- Following the wikipedia proof
  -- I don't think that the wikipedia proof technique of starting at n=1 is necessary, so I start at n = 0
  revert p hp S
  induction n with
  | zero =>
    intros p hp S
    -- Because p is a polynomial over the (empty) type Fin 0 of variables, it is constant
    rw [MvPolynomial.eq_C_of_isEmpty p] at *
    simp only [Nat.zero_eq, MvPolynomial.eval_C, Fin.forall_fin_zero_pi, Finset.filter_const,
      MvPolynomial.totalDegree_C, pow_zero, mul_one, nonpos_iff_eq_zero, mul_eq_zero,
      Finset.card_eq_zero, ite_eq_right_iff]
    left
    intro h
    simp [h] at hp
    -- Now, assume that the theorem holds for all polynomials in n variables.
  | succ n ih =>
    intros p p_nonzero S
    -- We can then consider p to be a polynomial over MvPolynomials in one fewer variables
    set p' : Polynomial (MvPolynomial (Fin n) F) := MvPolynomial.finSuccEquiv F n p with hp'
    -- since p is not identically zero, there is some i such that p_i' is not identically zero
    -- take the largest such i
    set i := p'.natDegree with hi
    set p_i' := Polynomial.coeff p' i with hp_i'
    have h0 : p_i'.totalDegree + i ≤ (p.totalDegree) := by
      apply MvPolynomial.totalDegree_coeff_finSuccEquiv_add_le
      rw [←Polynomial.leadingCoeff, Polynomial.leadingCoeff_ne_zero]
      exact Iff.mpr (AddEquivClass.map_ne_zero_iff (MvPolynomial.finSuccEquiv F n)) p_nonzero
    have h1 : p_i' ≠ 0 := by
      rw [hp_i', hi, ←Polynomial.leadingCoeff, Polynomial.leadingCoeff_ne_zero]
      exact Iff.mpr (AddEquivClass.map_ne_zero_iff (MvPolynomial.finSuccEquiv F n)) p_nonzero
    -- We use the inductive hypothesis on p_i'
    replace ih := ih p_i' h1 S

    -- -- TODO remove p from context now by reexpressing everthing in terms of p'?
    -- have fsdoifj : p = (MvPolynomial.finSuccEquiv F n).symm p' := by
    --   apply AlgEquiv_invFun_apply
    -- simp only [fsdoifj] at p

    -- We then split the set of possible zeros into a union of two cases:
    -- In the first case, p_i' evaluates to 0.
    have h_first_half :
      Finset.card
        (Finset.filter
          (fun r ↦ MvPolynomial.eval (r ∘ Fin.succ) p_i' = 0)
          (((Fintype.piFinset (fun _ => S)))))
      ≤
      (MvPolynomial.totalDegree p - i) * (Finset.card S) ^ n := by
      -- In this case, we bound the size of the set via the inductive hypothesis
      calc
        _ ≤ (MvPolynomial.totalDegree p_i') * (Finset.card S) ^ n := by
          convert ih
          rw [mul_comm]
          convert Finset.card_filter_succ_piFinset_eq ((fun f ↦ (MvPolynomial.eval (f)) p_i' = 0)) (fun _ => S)
        _ ≤ _ := by
          exact Nat.mul_le_mul_right (Finset.card S ^ n) (Nat.le_sub_of_add_le h0)
    save
    -- In the second case p_i' does not evaluate to zero.
    have h_second_half :
      Finset.card
          (Finset.filter
            (fun r ↦ MvPolynomial.eval r p = 0 ∧ MvPolynomial.eval (r ∘ Fin.succ) p_i' ≠ 0)
            ((Fintype.piFinset (fun _ => S))))
      ≤
      (i) * (Finset.card S) ^ n := by
      clear h_first_half

      -- In this case, given r on which p_i' does not evaluate to zero, p' mapped over the
      -- evaluation
      -- on r of p_i' is a nonzero univariate polynomial of degree i.
      -- There can therefore only be at most i zeros per r value.
      rw [←Finset.card_map (Equiv.toEmbedding (Equiv.piFinSucc n F)), Finset.map_filter,
        Finset.card_eq_sum_ones, Finset.sum_finset_product_right _
            (s := (Finset.filter (fun r ↦ (MvPolynomial.eval (r)) p_i' ≠ 0)
              (Fintype.piFinset (fun _ => S))))
            (t := fun r => Finset.filter (fun f => (MvPolynomial.eval ((Equiv.piFinSucc n F).invFun (f, r))) p = 0) S)] -- Note that ((Equiv.piFinSucc n F).invFun (f, r)) can be more simply written with Fin.cons
      · simp_rw [←Finset.card_eq_sum_ones]
        apply le_trans (Finset.sum_le_sum (g := fun _ => i) _)
        · rw [Finset.sum_const, smul_eq_mul, mul_comm]
          apply Nat.mul_le_mul_left
          apply le_trans (Finset.card_filter_le _ _)
          apply le_of_eq
          rw [Fintype.card_piFinset]
          simp only [Finset.prod_const, Finset.card_fin]
        · intros r hr
          simp only [Equiv.invFun_as_coe, Equiv.piFinSucc_symm_apply]
          simp_rw [MvPolynomial.eval_eq_eval_mv_eval']
          rw [←hp']
          simp only [←hp',
            Fintype.mem_piFinset, Finset.mem_filter] at hr
          -- hr2 is in wikipedia P_i(r_2, ... , r_n) ≠ 0
          rcases hr with ⟨hr1, hr2⟩
          -- my pr is wikis P(x_1, r_2, ... r_n) = ∑ x_1^i P_i(r_2, ... r_n)
          save
          set p_r := (Polynomial.map (MvPolynomial.eval r) p') with hp_r
          have : p_r.natDegree = i := by
            rw [←hi] at hr2
            rw [hp_r]
            rw [hi]
            apply Polynomial.natDegree_map_of_leadingCoeff_ne_zero
            -- rw [Polynomial.natDegree_map_eq_iff (f := MvPolynomial.eval r) p']
            unfold Polynomial.leadingCoeff
            exact hr2
          rw [←hi, ←this]
          apply le_trans _ (Polynomial.card_roots' _)
          apply le_trans _ (Multiset.toFinset_card_le _)
          apply Finset.card_le_of_subset
          rw [Finset.subset_iff]
          intro x
          rw [Finset.mem_filter,
            Multiset.mem_toFinset, Polynomial.mem_roots', ne_eq, and_imp]
          intros XS hxr
          rw [Polynomial.IsRoot.def]
          rw [hxr]
          -- rw [refl]
          simp only [←hp_r, and_true]
          intro hpr_zero
          contrapose! hr2
          rw [←hp'] at *
          rw [hpr_zero] at this
          rw [Polynomial.natDegree_zero] at this
          rw [←hi, ←this]
          have hp_r0 : p_r.coeff 0 = 0 := by simp [hpr_zero]
          rw [←hp_r0]
          rw [Polynomial.coeff_map]
      · -- Note Polynomial.coeff_natDegree, MvPolynomial.finSuccEquiv_apply, MvPolynomial.coe_eval₂Hom, are triggering but I don't want them
        simp only [
          Equiv.piFinSucc_symm_apply, Finset.mem_map_equiv, Fintype.mem_piFinset, Function.comp_apply,
          Prod.forall, Finset.mem_filter, Equiv.invFun_as_coe]
        intros a b
        -- TODO write unfold_projs tactic in Lean 4

        constructor
        · intro hfr
          rcases hfr with ⟨hfr1, hfr2, hfr3⟩
          constructor
          · constructor
            · intro n'
              refine hfr1 (Fin.succ n')
            · exact hfr3
          · constructor
            · refine hfr1 0
            · exact hfr2
        · intro hab
          rcases hab with ⟨⟨hab1, hab1'⟩, hab2, hab3⟩
          rw [←Fintype.mem_piFinset]
          simp only [Fintype.mem_piFinset]
          simp_rw [Fin.forall_fin_succ]
          constructor
          · simp [hab1, hab2]
          · exact ⟨hab3, hab1'⟩


    -- Putting these results together, we take a union bound over these two cases to finish the
    -- proof
    calc
      -- Pr[A]
      Finset.card
        (Finset.filter
          (fun r ↦ MvPolynomial.eval r p = 0)
          (Fintype.piFinset (fun _ => S)))
      * Finset.card S
      =
      -- Pr [A ∩ B] + Pr [A ∩ Bᶜ]
      (Finset.card
        (Finset.filter
          (fun r ↦ MvPolynomial.eval r p = 0 ∧ MvPolynomial.eval (r ∘ Fin.succ) p_i' = 0)
          (Fintype.piFinset (fun _ => S)))
      +
      Finset.card
        (Finset.filter
          (fun r ↦ MvPolynomial.eval r p = 0 ∧ MvPolynomial.eval (r ∘ Fin.succ) p_i' ≠ 0)
          (Fintype.piFinset (fun _ => S)))
      )
      * Finset.card S := by
        congr
        rw [←Finset.card_union_add_card_inter]
        rw [Finset.filter_union_right]
        -- todo note filter_or is the symm of this. Golf that proof.
        rw [←Finset.filter_and]
        simp only [ne_eq, and_or_and_not_iff, and_and_and_not_iff]
        simp only [Finset.filter_False, Finset.card_empty, add_zero]
      -- Pr [B] + Pr [A ∩ Bᶜ]
      _ ≤ (Finset.card
        (Finset.filter
          (fun r ↦ MvPolynomial.eval (r ∘ Fin.succ) p_i' = 0)
          (Fintype.piFinset (fun _ => S)))
      +
      Finset.card
        (Finset.filter
          (fun r ↦ MvPolynomial.eval r p = 0 ∧ MvPolynomial.eval (r ∘ Fin.succ) p_i' ≠ 0)
          (Fintype.piFinset (fun _ => S)))
      )
      * Finset.card S := by
        apply Nat.mul_le_mul_right
        rw [add_le_add_iff_right]
        apply Finset.card_le_of_subset
        apply Finset.monotone_filter_right
        rw [Pi.le_def]
        intro i
        rename_i inst inst_1 inst_2 i_1
        simp_all only [ne_eq, MvPolynomial.finSuccEquiv_apply, MvPolynomial.coe_eval₂Hom, Polynomial.coeff_natDegree,
          Polynomial.leadingCoeff_eq_zero, ge_iff_le, not_and, not_not, le_Prop_eq, and_imp, implies_true]
      _ ≤ ((MvPolynomial.totalDegree p - i) * (Finset.card S) ^ n
          +
          (i) * (Finset.card S) ^ n
          )
      * Finset.card S := by
        apply Nat.mul_le_mul_right
        apply add_le_add
        exact h_first_half
        exact h_second_half
      _ ≤
      MvPolynomial.totalDegree p * Finset.card S ^ Nat.succ n := by
        rw [Nat.pow_succ]
        rw [←mul_assoc]
        apply Nat.mul_le_mul_right
        rw [←add_mul]
        apply Nat.mul_le_mul_right
        apply le_of_eq
        apply Nat.sub_add_cancel
        apply le_of_add_le_right h0
