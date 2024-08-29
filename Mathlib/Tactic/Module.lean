/-
Copyright (c) 2024 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Mathlib.Algebra.Algebra.Tower
import Mathlib.GroupTheory.GroupAction.BigOperators
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.Util.AtomM

/-! # A tactic for normalization over modules
-/

open Lean hiding Module
open Meta Elab Qq Mathlib.Tactic

abbrev smulAndSum {R : Type*} {M : Type*} [SMul R M] [Add M] [Zero M] (l : List (R × M)) : M :=
  (l.map (fun (⟨r, x⟩ : R × M) ↦ r • x)).sum

@[simp] theorem smulAndSum_cons {R : Type*} {M : Type*} [SMul R M] [AddMonoid M] (p : R × M)
    (l : List (R × M)) :
    smulAndSum (p :: l) = p.1 • p.2 + smulAndSum l := by
  unfold smulAndSum
  dsimp only
  rw [List.map_cons]
  rw [List.sum_cons]

abbrev List.onFst {α β γ : Type*} (l : List (α × β)) (f : α → γ) : List (γ × β) :=
  l.map (fun p ↦ ⟨f p.1, p.2⟩)

abbrev considerFstAs {S M : Type*} (R : Type*) [CommSemiring S] [Semiring R] [Algebra S R] :
    (S × M) → (R × M) :=
  fun ⟨s, x⟩ ↦ (algebraMap S R s, x)

theorem smulAndSum_considerFstAs {S : Type*} (R : Type*) {M : Type*} [CommSemiring S] [Semiring R]
    [Algebra S R] [AddMonoid M] [SMul S M] [MulAction R M] [IsScalarTower S R M]
    (l : List (S × M)) :
    smulAndSum (l.map (considerFstAs R)) = smulAndSum l := by
  simp only [smulAndSum, List.map_map]
  congr
  ext
  simp [IsScalarTower.algebraMap_smul]

theorem eq_smulAndSum_considerFstAs {S : Type*} (R : Type*) {M : Type*} [CommSemiring S]
    [Semiring R] [Algebra S R] [AddMonoid M] [SMul S M] [MulAction R M] [IsScalarTower S R M]
    {x : M} {l : List (S × M)} (h : x = smulAndSum l) :
    x = smulAndSum (l.map (considerFstAs R)) := by
  rw [smulAndSum_considerFstAs, h]

abbrev combine {α : Type*} (f : α → α → α) (fL : α → α) (fR : α → α) :
    List (α × ℕ) → List (α × ℕ) → List (α × ℕ)
  | [], l => l.onFst fR
  | l@(_ :: _), [] => l.onFst fL
  | (a₁, k₁) :: t₁, (a₂, k₂) :: t₂ =>
    if k₁ < k₂ then
      (fL a₁, k₁) :: combine f fL fR t₁ ((a₂, k₂) :: t₂)
    else if k₁ = k₂ then
      (f a₁ a₂, k₁) :: combine f fL fR t₁ t₂
    else
      (fR a₂, k₂) :: combine f fL fR ((a₁, k₁) :: t₁) t₂

abbrev cob' {M : Type*} {R : Type} [Semiring R] (p₁ p₂ : R × M) : R × M :=
  let r₁ := Prod.fst p₁
  let r₂ := Prod.fst p₂
  let m₁ := Prod.snd p₁
  (r₁ + r₂, m₁)

abbrev cob {v : Level} {M : Q(Type v)} {R : Q(Type)} (_i₂ : Q(Semiring $R)) (p₁ p₂ : Q($R × $M)) :
    Q($R × $M) :=
  q(cob' $p₁ $p₂)

abbrev boc' {M : Type*} {R : Type} [Ring R] (p₁ p₂ : R × M) : R × M :=
  let r₁ := Prod.fst p₁
  let r₂ := Prod.fst p₂
  let m₁ := Prod.snd p₁
  (r₁ - r₂, m₁)

abbrev boc {v : Level} {M : Q(Type v)} {R : Q(Type)} (_i₂ : Q(Ring $R))
    (p₁ p₂ : Q($R × $M)) :
    Q($R × $M) :=
  q(boc' $p₁ $p₂)

abbrev bco' (M : Type*) (R : Type) [Ring R] (p : R × M) : R × M :=
  let r := Prod.fst p
  let m := Prod.snd p
  (- r, m)

abbrev bco {v : Level} {M : Q(Type v)} {R : Q(Type)} (_i₂ : Q(Ring $R))
    (p : Q($R × $M)) :
    Q($R × $M) :=
  q(@bco' $M $R $_i₂ $p)

theorem one_pf {M : Type*} [AddMonoid M] (x : M) : x = smulAndSum [((1:ℕ), x)] := by
  simp [smulAndSum]

theorem zero_pf (M : Type*) [AddMonoid M] : (0:M) = smulAndSum (R := Nat) [] := by simp [smulAndSum]

def List.quote {v : Level} {α : Q(Type v)} : List (Q($α)) → Q(List $α)
  | [] => q([])
  | e :: t => q($e :: $(t.quote))

def matchRings {v : Level} (M : Q(Type v)) (iM : Q(AddCommMonoid $M)) (x₁ x₂ : Q($M))
    {R₁ : Q(Type)} {iR₁ : Q(Semiring $R₁)} (iRM₁ : Q(@Module $R₁ $M $iR₁ $iM))
    (l₁ : List (Q($R₁ × $M) × ℕ)) (pf₁ : Q($x₁ = smulAndSum $((l₁.map Prod.fst).quote)))
    {R₂ : Q(Type)} {iR₂ : Q(Semiring $R₂)} (iRM₂ : Q(@Module $R₂ $M $iR₂ $iM))
    (l₂ : List (Q($R₂ × $M) × ℕ)) (pf₂ : Q($x₂ = smulAndSum $((l₂.map Prod.fst).quote))) :
    MetaM <| Σ R : Q(Type), Σ iR : Q(Semiring $R), Σ _ : Q(@Module $R $M $iR $iM),
      Σ l₁ l₂ : List (Q($R × $M) × ℕ),
      Q($x₁ = smulAndSum $((l₁.map Prod.fst).quote))
        × Q($x₂ = smulAndSum $((l₂.map Prod.fst).quote)) := do
  match ← isDefEqQ R₁ R₂ with
  -- this case is handled separately, so as not to require commutativity if `R₁ = R₂`
  | .defEq (_ : $R₁ =Q $R₂) => pure ⟨R₁, iR₁, iRM₁, l₁, l₂, pf₁, pf₂⟩
  -- otherwise the "smaller" of the two rings must be commutative
  | _ =>
  try
    let _i₁ ← synthInstanceQ q(CommSemiring $R₁)
    let _i₃ ← synthInstanceQ q(Algebra $R₁ $R₂)
    let _i₄ ← synthInstanceQ q(IsScalarTower $R₁ $R₂ $M)
    assumeInstancesCommute
    let l₁' : List (Q($R₂ × $M) × ℕ) := l₁.onFst (fun p ↦ q(considerFstAs $R₂ $p))
    pure ⟨R₂, iR₂, iRM₂, l₁', l₂, (q(eq_smulAndSum_considerFstAs $R₂ $pf₁):), pf₂⟩
  catch _ =>
    let _i₁ ← synthInstanceQ q(CommSemiring $R₂)
    let _i₃ ← synthInstanceQ q(Algebra $R₂ $R₁)
    let _i₄ ← synthInstanceQ q(IsScalarTower $R₂ $R₁ $M)
    assumeInstancesCommute
    let l₂' : List (Q($R₁ × $M) × ℕ) := l₂.onFst (fun p ↦ q(considerFstAs $R₁ $p))
    pure ⟨R₁, iR₁, iRM₁, l₁, l₂', pf₁, (q(eq_smulAndSum_considerFstAs $R₁ $pf₂):)⟩

def matchRings' {v : Level} (M : Q(Type v)) (iM : Q(AddCommMonoid $M)) (x : Q($M))
    {R₁ : Q(Type)} {iR₁ : Q(Semiring $R₁)} (iRM₁ : Q(@Module $R₁ $M $iR₁ $iM))
    (l : List (Q($R₁ × $M) × ℕ)) (pf : Q($x = smulAndSum $((l.map Prod.fst).quote)))
    {R₂ : Q(Type)} (iR₂ : Q(Semiring $R₂)) (iRM₂ : Q(@Module $R₂ $M $iR₂ $iM)) (r₂ : Q($R₂)) :
    MetaM <| Σ R : Q(Type), Σ iR : Q(Semiring $R), Σ _ : Q(@Module $R $M $iR $iM),
      Σ l : List (Q($R × $M) × ℕ),
      Q($x = smulAndSum $((l.map Prod.fst).quote))
        × Σ r : Q($R), Q($r₂ • $x = $r • $x) := do
  match ← isDefEqQ R₁ R₂ with
  -- this case is handled separately, so as not to require commutativity if `R₁ = R₂`
  | .defEq (_ : $R₁ =Q $R₂) => pure ⟨R₁, iR₁, iRM₁, l, pf, r₂, (q(@rfl _ ($r₂ • $x)):)⟩
  -- otherwise the "smaller" of the two rings must be commutative
  | _ =>
  try
    let _i₁ ← synthInstanceQ q(CommSemiring $R₁)
    let _i₃ ← synthInstanceQ q(Algebra $R₁ $R₂)
    let _i₄ ← synthInstanceQ q(IsScalarTower $R₁ $R₂ $M)
    assumeInstancesCommute
    let l' : List (Q($R₂ × $M) × ℕ) := l.onFst (fun p ↦ q(considerFstAs $R₂ $p))
    let pf' : Q($r₂ • $x = $r₂ • $x) := q(rfl)
    pure ⟨R₂, iR₂, iRM₂, l', (q(eq_smulAndSum_considerFstAs $R₂ $pf):), r₂, pf'⟩
  catch _ =>
    let _i₁ ← synthInstanceQ q(CommSemiring $R₂)
    let _i₃ ← synthInstanceQ q(Algebra $R₂ $R₁)
    let _i₄ ← synthInstanceQ q(IsScalarTower $R₂ $R₁ $M)
    assumeInstancesCommute
    let r : Q($R₁) := q(algebraMap $R₂ $R₁ $r₂)
    let pf' : Q($r₂ • $x = $r • $x) := q(Eq.symm (IsScalarTower.algebraMap_smul $R₁ $r₂ $x))
    pure ⟨R₁, iR₁, iRM₁, l, pf, r, pf'⟩

def liftRing {v : Level} (M : Q(Type v)) (iM : Q(AddCommMonoid $M)) (x₁ : Q($M))
    {R₁ : Q(Type)} {iR₁ : Q(Semiring $R₁)} (iRM₁ : Q(@Module $R₁ $M $iR₁ $iM))
    (l₁ : List (Q($R₁ × $M) × ℕ)) (pf₁ : Q($x₁ = smulAndSum $((l₁.map Prod.fst).quote)))
    (R₂ : Q(Type)) (iR₂ : Q(Semiring $R₂)) (iRM₂ : Q(@Module $R₂ $M $iR₂ $iM)) :
    MetaM <| Σ R : Q(Type), Σ iR : Q(Semiring $R), Σ _ : Q(@Module $R $M $iR $iM),
      Σ l₁ : List (Q($R × $M) × ℕ), Q($x₁ = smulAndSum $((l₁.map Prod.fst).quote)) := do
  match ← isDefEqQ R₁ R₂ with
  -- this case is handled separately, so as not to require commutativity if `R₁ = R₂`
  | .defEq (_ : $R₁ =Q $R₂) => pure ⟨R₁, iR₁, iRM₁, l₁, pf₁⟩
  -- otherwise the "smaller" of the two rings must be commutative
  | _ =>
  try
    let _i₁ : Q(CommSemiring $R₂) ← synthInstanceQ q(CommSemiring $R₂)
    let _i₃ ← synthInstanceQ q(Algebra $R₂ $R₁)
    let _i₄ ← synthInstanceQ q(IsScalarTower $R₂ $R₁ $M)
    pure ⟨R₁, iR₁, iRM₁, l₁, pf₁⟩
  catch _ =>
    let _i₁ ← synthInstanceQ q(CommSemiring $R₁)
    let _i₃ ← synthInstanceQ q(Algebra $R₁ $R₂)
    let _i₄ ← synthInstanceQ q(IsScalarTower $R₁ $R₂ $M)
    assumeInstancesCommute
    let l₁' : List (Q($R₂ × $M) × ℕ) := l₁.onFst (fun p ↦ q(considerFstAs $R₂ $p))
    pure ⟨R₂, iR₂, iRM₂, l₁', (q(eq_smulAndSum_considerFstAs $R₂ $pf₁):)⟩


theorem smulAndSum_cons_add_cons₁ {R : Type*} {M : Type*} [SMul R M] [AddMonoid M]
    (a₁ a₂ : R × M) (l₁ l₂ : List (R × M)):
    smulAndSum (a₁ :: l₁) + smulAndSum (a₂ :: l₂)
      = a₁.1 • a₁.2 + (smulAndSum l₁ + smulAndSum (a₂ :: l₂)) := by
  rw [smulAndSum_cons]
  rw [add_assoc]

theorem smulAndSum_cons_sub_cons₁ {R : Type*} {M : Type*} [SMul R M] [AddGroup M]
    (a₁ a₂ : R × M) (l₁ l₂ : List (R × M)):
    smulAndSum (a₁ :: l₁) - smulAndSum (a₂ :: l₂)
      = a₁.1 • a₁.2 + (smulAndSum l₁ - smulAndSum (a₂ :: l₂)) := by
  rw [smulAndSum_cons]
  rw [add_sub_assoc]

theorem smulAndSum_cons_add_cons₂ {R : Type*} {M : Type*} [SMul R M] [AddCommMonoid M]
    (a₁ a₂ : R × M) (l₁ l₂ : List (R × M)):
    smulAndSum (a₁ :: l₁) + smulAndSum (a₂ :: l₂)
      = (a₁.1 • a₁.2 + a₂.1 • a₂.2) + (smulAndSum l₁ + smulAndSum l₂) := by
  simp [smulAndSum_cons, add_assoc]
  congr! 1
  simp [← add_assoc]
  congr! 1
  rw [add_comm]

theorem smulAndSum_cons_sub_cons₂ {R : Type*} {M : Type*} [SMul R M] [AddCommGroup M]
    (a₁ a₂ : R × M) (l₁ l₂ : List (R × M)):
    smulAndSum (a₁ :: l₁) - smulAndSum (a₂ :: l₂)
      = (a₁.1 • a₁.2 - a₂.1 • a₂.2) + (smulAndSum l₁ - smulAndSum l₂) := by
  simp [smulAndSum_cons]
  abel

theorem smulAndSum_cons_add_cons₃ {R : Type*} {M : Type*} [SMul R M] [AddCommMonoid M]
    (a₁ a₂ : R × M) (l₁ l₂ : List (R × M)) :
    smulAndSum (a₁ :: l₁) + smulAndSum (a₂ :: l₂)
      = a₂.1 • a₂.2 + (smulAndSum (a₁ :: l₁) + smulAndSum l₂) := by
  simp [smulAndSum_cons, ← add_assoc]
  congr! 1
  simp only [add_comm _ (smulAndSum _), add_assoc]
  congr! 1
  rw [add_comm]

theorem smulAndSum_cons_sub_cons₃ {R : Type*} {M : Type*} [SMul R M] [AddCommGroup M]
    (a₁ a₂ : R × M) (l₁ l₂ : List (R × M)) :
    smulAndSum (a₁ :: l₁) - smulAndSum (a₂ :: l₂)
      = -(a₂.1 • a₂.2) + (smulAndSum (a₁ :: l₁) - smulAndSum l₂) := by
  simp [smulAndSum_cons]
  abel

theorem smulAndSum_neg {M : Type*} [AddCommGroup M] {R : Type*} [Ring R] [Module R M]
    (l : List (R × M)) :
    smulAndSum (l.onFst Neg.neg) = - smulAndSum l := by
  simp only [smulAndSum, List.map_map, List.sum_neg]
  congr
  ext p
  simp

theorem neg_eq_smulAndSum {M : Type*} [AddCommGroup M] {R : Type*} [Ring R] [Module R M]
    {l : List (R × M)} {x : M} (h : x = smulAndSum l) :
    - x = smulAndSum (l.onFst Neg.neg) := by
  simpa [smulAndSum_neg]

theorem smul_eq_smulAndSum {M : Type*} [AddCommMonoid M] {R : Type*} [Semiring R] [Module R M]
    {l : List (R × M)} {x : M} (h : x = smulAndSum l) (r : R) :
    r • x = smulAndSum (l.onFst (r * ·)) := by
  unfold smulAndSum at h ⊢
  simp only [List.map_map, h, List.smul_sum]
  congr
  ext p
  simp [mul_smul]


theorem askaf {α β : Type*} (k₁ k₂ : ℕ) (l₁ l₂ l₃ : List (α × β)) :
    (if k₁ < k₂ then l₁.map Prod.fst else if k₁ = k₂ then l₂.map Prod.fst else l₃.map Prod.fst)
    = (if k₁ < k₂ then l₁ else if k₁ = k₂ then l₂ else l₃).map Prod.fst := by
  split_ifs <;> rfl

def ugh {v : Level} {α : Q(Type v)} {a₁ a₂ : Q($α)} (h : a₁ = a₂) : Q($a₁ = $a₂) := by
  rw [h]
  exact q(rfl)

def mkSmulAndSum_add {v : Level} {M : Q(Type v)} {R : Q(Type)} {iR : Q(Semiring $R)}
    {iM : Q(AddCommMonoid $M)} (iRM : Q(Module $R $M)) (l₁ l₂ : List (Q($R × $M) × ℕ)) :
    Q(smulAndSum $((l₁.map Prod.fst).quote) + smulAndSum $((l₂.map Prod.fst).quote)
      = smulAndSum $(((combine (cob iR) id id l₁ l₂).map Prod.fst).quote)) :=
  match l₁, l₂ with
  | [], l => (q(zero_add (smulAndSum $((l.map Prod.fst).quote))):)
  | l@(_ :: _), [] => (q(add_zero (smulAndSum $((l.map Prod.fst).quote))):)
  | (a₁, k₁) :: t₁, (a₂, k₂) :: t₂ =>
    let z₁ : Q(List ($R × $M)) := (t₁.map Prod.fst).quote
    let z₂ : Q(List ($R × $M)) := (t₂.map Prod.fst).quote
    let l₁ : Q(List ($R × $M)) :=
      List.quote ((combine (cob iR) id id t₁ ((a₂, k₂) :: t₂)).map Prod.fst)
    let A : Q($R × $M) := cob iR a₁ a₂
    let l₂ : Q(List ($R × $M)) :=
      List.quote ((combine (cob iR) id id t₁ t₂).map Prod.fst)
    let l₃ : Q(List ($R × $M)) :=
      List.quote ((combine (cob iR) id id ((a₁, k₁) :: t₁) t₂).map Prod.fst)
    let pf₁ : Q($a₁.1 • $a₁.2 + (smulAndSum $z₁ + smulAndSum ($a₂ :: $z₂))
        = $a₁.1 • $a₁.2 + smulAndSum $l₁) :=
      q(congrArg _ $(mkSmulAndSum_add iRM t₁ ((a₂, k₂) :: t₂)))
    let pf₂' : Q(($a₁.1 • $a₁.2 + $a₂.1 • $a₂.2) = $A.1 • $A.2) :=
      (q(Eq.symm (add_smul $a₁.1 $a₂.1 $A.2)):)
    let pf₂ : Q(($a₁.1 • $a₁.2 + $a₂.1 • $a₂.2) + (smulAndSum $z₁ + smulAndSum $z₂)
        = $A.1 • $A.2 + smulAndSum $l₂) :=
      q(congrArg₂ (· + ·) $pf₂' $(mkSmulAndSum_add iRM t₁ t₂))
    let pf₃ : Q($a₂.1 • $a₂.2 + (smulAndSum ($a₁ :: $z₁) + smulAndSum $z₂)
        = $a₂.1 • $a₂.2 +  smulAndSum $l₃) :=
      q(congrArg _ $(mkSmulAndSum_add iRM ((a₁, k₁) :: t₁) t₂))
    let l' : Q(List ($R × $M)) :=
      if k₁ < k₂ then q($a₁ :: $l₁) else if k₁ = k₂ then q($A :: $l₂) else q($a₂ :: $l₃)
    let pf_lhs : Q((smulAndSum ($a₁ :: $z₁)) + (smulAndSum ($a₂ :: $z₂)) = smulAndSum $l') :=
      if k₁ < k₂ then
        (q(Eq.trans (smulAndSum_cons_add_cons₁ _ _ _ _)
          (Eq.trans $pf₁ (Eq.symm (smulAndSum_cons _ _)))) : Expr)
      else if k₁ = k₂ then
        (q(Eq.trans (smulAndSum_cons_add_cons₂ _ _ _ _)
          (Eq.trans $pf₂ (Eq.symm (smulAndSum_cons _ _)))) : Expr)
      else
        (q(Eq.trans (smulAndSum_cons_add_cons₃ _ _ _ _)
          (Eq.trans $pf₃ (Eq.symm (smulAndSum_cons _ _)))) : Expr)
    let p₁ : List (Q($R × $M) × ℕ) := (a₁, k₁) :: combine (cob iR) id id t₁ ((a₂, k₂) :: t₂)
    let p₂ : List (Q($R × $M) × ℕ) := (cob iR a₁ a₂, k₁) :: combine (cob iR) id id t₁ t₂
    let p₃ : List (Q($R × $M) × ℕ) := (a₂, k₂) :: combine (cob iR) id id ((a₁, k₁) :: t₁) t₂
    let l'' : Q(List ($R × $M)) := List.quote <|
      if k₁ < k₂ then
        List.map Prod.fst <| p₁
      else if k₁ = k₂ then
        List.map Prod.fst <| p₂
      else
        List.map Prod.fst <| p₃
    let l : Q(List ($R × $M)) := List.quote <| List.map Prod.fst <|
      if k₁ < k₂ then
        p₁
      else if k₁ = k₂ then
        p₂
      else
        p₃
    have e : l'' = l := congrArg List.quote (askaf k₁ k₂ p₁ p₂ p₃)
    let noooo : Q($l'' = $l) := ugh e -- juggle `apply_ite`
    let pf_rhs : Q(smulAndSum $l' = smulAndSum $l) := (q(congrArg smulAndSum $noooo):)
    (q(Eq.trans $pf_lhs $pf_rhs):)

def mkSmulAndSum_sub {v : Level} {M : Q(Type v)} {R : Q(Type)} (iR : Q(Ring $R))
    (iM : Q(AddCommGroup $M)) (iRM : Q(Module $R $M)) (l₁ l₂ : List (Q($R × $M) × ℕ)) :
    Q(smulAndSum $((l₁.map Prod.fst).quote) - smulAndSum $((l₂.map Prod.fst).quote)
      = smulAndSum $(((combine (boc iR) id (bco iR) l₁ l₂).map Prod.fst).quote)) :=
  match l₁, l₂ with
  | [], l =>
    let L := l.map Prod.fst
    let pf₁ : Q(0 - smulAndSum $(L.quote) = - smulAndSum $(L.quote)) :=
      (q(zero_sub (smulAndSum $(L.quote))):)
    let pf₂ : Q(smulAndSum $((L.map (bco iR)).quote) = - smulAndSum $(L.quote)) :=
      (q(smulAndSum_neg $(L.quote)):)
    (q(Eq.trans $pf₁ (Eq.symm $pf₂)):)
  | l@(_ :: _), [] => (q(sub_zero (smulAndSum $((l.map Prod.fst).quote))):)
  | (a₁, k₁) :: t₁, (a₂, k₂) :: t₂ =>
    let z₁ : Q(List ($R × $M)) := (t₁.map Prod.fst).quote
    let z₂ : Q(List ($R × $M)) := (t₂.map Prod.fst).quote
    let l₁ : Q(List ($R × $M)) :=
      List.quote ((combine (boc iR) id (bco iR) t₁ ((a₂, k₂) :: t₂)).map Prod.fst)
    let A : Q($R × $M) := boc iR a₁ a₂
    let B : Q($R × $M) := bco iR a₂
    let l₂ : Q(List ($R × $M)) :=
      List.quote ((combine (boc iR) id (bco iR) t₁ t₂).map Prod.fst)
    let l₃ : Q(List ($R × $M)) :=
      List.quote ((combine (boc iR) id (bco iR) ((a₁, k₁) :: t₁) t₂).map Prod.fst)
    let pf₁ : Q($a₁.1 • $a₁.2 + (smulAndSum $z₁ - smulAndSum ($a₂ :: $z₂))
        = $a₁.1 • $a₁.2 + smulAndSum $l₁) :=
      q(congrArg _ $(mkSmulAndSum_sub iR iM iRM t₁ ((a₂, k₂) :: t₂)))
    let pf₂' : Q(($a₁.1 • $a₁.2 - $a₂.1 • $a₂.2) = $A.1 • $A.2) :=
      (q(Eq.symm (sub_smul $a₁.1 $a₂.1 $A.2)):)
    let pf₂ : Q(($a₁.1 • $a₁.2 - $a₂.1 • $a₂.2) + (smulAndSum $z₁ - smulAndSum $z₂)
        = $A.1 • $A.2 + smulAndSum $l₂) :=
      q(congrArg₂ (· + ·) $pf₂' $(mkSmulAndSum_sub iR iM iRM t₁ t₂))
    let pf₃' : Q(-($a₂.1 • $a₂.2) = $B.1 • $B.2) := q(Eq.symm (neg_smul _ _))
    let pf₃ : Q(-($a₂.1 • $a₂.2) + (smulAndSum ($a₁ :: $z₁) - smulAndSum $z₂)
        = $B.1 • $B.2 +  smulAndSum $l₃) :=
      q(congrArg₂ (· + ·) $pf₃' $(mkSmulAndSum_sub iR iM iRM ((a₁, k₁) :: t₁) t₂))
    let x₁ : Q(List ($R × $M)) := q(List.cons ($a₁) $l₁)
    let x₂ : Q(List ($R × $M)) := q(List.cons ($A) $l₂)
    let x₃ : Q(List ($R × $M)) := q(List.cons ($B) $l₃)
    let l' : Q(List ($R × $M)) := if k₁ < k₂ then x₁ else if k₁ = k₂ then x₂ else x₃
    let pf_lhs : Q((smulAndSum ($a₁ :: $z₁)) - (smulAndSum ($a₂ :: $z₂)) = smulAndSum $l') :=
      if k₁ < k₂ then
        (q(Eq.trans (smulAndSum_cons_sub_cons₁ _ _ _ _)
          (Eq.trans $pf₁ (Eq.symm (smulAndSum_cons _ _)))) : Expr)
      else if k₁ = k₂ then
        (q(Eq.trans (smulAndSum_cons_sub_cons₂ _ _ _ _)
          (Eq.trans $pf₂ (Eq.symm (smulAndSum_cons _ _)))) : Expr)
      else
        (q(Eq.trans (smulAndSum_cons_sub_cons₃ _ _ _ _)
          (Eq.trans $pf₃ (Eq.symm (smulAndSum_cons _ _)))) : Expr)
    let p₁ : List (Q($R × $M) × ℕ) := (a₁, k₁) :: combine (boc iR) id (bco iR) t₁ ((a₂, k₂) :: t₂)
    let p₂ : List (Q($R × $M) × ℕ) := (boc iR a₁ a₂, k₁) :: combine (boc iR) id (bco iR) t₁ t₂
    let p₃ : List (Q($R × $M) × ℕ) :=
      (bco iR a₂, k₂) :: combine (boc iR) id (bco iR) ((a₁, k₁) :: t₁) t₂
    let l'' : Q(List ($R × $M)) := List.quote <|
      if k₁ < k₂ then
        List.map Prod.fst <| p₁
      else if k₁ = k₂ then
        List.map Prod.fst <| p₂
      else
        List.map Prod.fst <| p₃
    let l : Q(List ($R × $M)) := List.quote <| List.map Prod.fst <|
      if k₁ < k₂ then
        p₁
      else if k₁ = k₂ then
        p₂
      else
        p₃
    have e : l'' = l := congrArg List.quote (askaf k₁ k₂ p₁ p₂ p₃)
    let noooo : Q($l'' = $l) := ugh e -- juggle `apply_ite`
    let pf_rhs : Q(smulAndSum $l' = smulAndSum $l) := (q(congrArg smulAndSum $noooo):)
    let pf : Q((smulAndSum ($a₁ :: $z₁)) - (smulAndSum ($a₂ :: $z₂)) = smulAndSum $l) :=
      q(Eq.trans $pf_lhs $pf_rhs)
    pf

/-- The main algorithm behind the `match_scalars` and `module` tactics: partially-normalizing an
expression in an additive commutative monoid `M` into the form c1 • x1 + c2 • x2 + ... c_k • x_k,
where x1, x2, ... are distinct atoms in `M`, and c1, c2, ... are scalars. The scalar type of the
expression is not pre-determined: instead it starts as `ℕ` (when each atom is initially given a
scalar `(1:ℕ)`) and gets bumped up into bigger semirings when such semirings are encountered.

It is assumed that there is a "linear order" on all the semirings which appear in the expression:
for any two semirings `R` and `S` which occur, we have either `Algebra R S` or `Algebra S R`).
(TODO: implement a variant in which a semiring `R` is provided by the user, and the assumption is
instead that for any semiring `S` which occurs, we have `Algebra S R`.) -/
partial def parse {v : Level} (M : Q(Type v)) (iM : Q(AddCommMonoid $M)) (x : Q($M)) :
    AtomM (Σ R : Q(Type), Σ iR : Q(Semiring $R), Σ _ : Q(@Module $R $M $iR $iM),
      Σ l : List (Q($R × $M) × ℕ), Q($x = smulAndSum $((l.map Prod.fst).quote))) := do
  match x with
  -- parse an addition: `x₁ + x₂`
  | ~q($x₁ + $x₂) =>
    let ⟨_, _, iRM₁, l₁', pf₁'⟩ ← parse M iM x₁
    let ⟨_, _, iRM₂, l₂', pf₂'⟩ ← parse M iM x₂
    -- lift from the semirings of scalars parsed from `x₁`, `x₂` (say `R₁`, `R₂`) to `R₁ ⊗ R₂`
    let ⟨R, iR, iRM, l₁, l₂, (pf₁ : Q($x₁ = smulAndSum $((l₁.map Prod.fst).quote))),
      (pf₂ : Q($x₂ = smulAndSum $((l₂.map Prod.fst).quote)))⟩
      ← matchRings M iM x₁ x₂ iRM₁ l₁' pf₁' iRM₂ l₂' pf₂'
    -- build the new list and proof
    let l := combine (cob iR) id id l₁ l₂
    let pf := mkSmulAndSum_add iRM l₁ l₂
    pure ⟨R, iR, iRM, l, (q(Eq.trans (congrArg₂ (· + ·) $pf₁ $pf₂) $pf):)⟩
  -- parse a subtraction: `x₁ - x₂`
  | ~q(@HSub.hSub _ _ _ (@instHSub _ $iM') $x₁ $x₂) =>
    let ⟨_, _, iRM₁, l₁, pf₁⟩ ← parse M iM x₁
    let ⟨_, _, iRM₂, l₂, pf₂⟩ ← parse M iM x₂
    -- lift from the semirings of scalars parsed from `x₁`, `x₂` (say `R₁`, `R₂`) to `R₁ ⊗ R₂ ⊗ ℤ`
    let iMZ ← synthInstanceQ q(Module ℤ $M)
    let ⟨_, _, iRM₁', l₁', pf₁'⟩ ← liftRing M iM x₁ iRM₁ l₁ pf₁ q(ℤ) q(Int.instSemiring) iMZ
    let ⟨_, _, iRM₂', l₂', pf₂'⟩ ← liftRing M iM x₂ iRM₂ l₂ pf₂ q(ℤ) q(Int.instSemiring) iMZ
    let ⟨R, iR, iRM, l₁'', l₂'', pf₁'', pf₂''⟩ ← matchRings M iM x₁ x₂ iRM₁' l₁' pf₁' iRM₂' l₂' pf₂'
    let iR' ← synthInstanceQ q(Ring $R)
    -- build the new list and proof
    let l := combine (boc iR') id (bco iR') l₁'' l₂''
    let iM' ← synthInstanceQ q(AddCommGroup $M)
    let pf : Q(smulAndSum $((l₁''.map Prod.fst).quote) - smulAndSum $((l₂''.map Prod.fst).quote)
      = smulAndSum $((l.map Prod.fst).quote)) := mkSmulAndSum_sub iR' iM' iRM l₁'' l₂''
    pure ⟨R, iR, iRM, l, q(Eq.trans (congrArg₂ (· - ·) $pf₁'' $pf₂'') $pf)⟩
  -- parse a negation: `-y`
  | ~q(@Neg.neg _ $iM' $y) =>
    let ⟨_, _, iRM₀, l₀, pf₀⟩ ← parse M iM y
    let iZ ← synthInstanceQ q(Semiring ℤ)
    let _i ← synthInstanceQ q(AddCommGroup $M)
    let iMZ ← synthInstanceQ q(Module ℤ $M)
    -- lift from original semiring of scalars (say `R₀`) to `R₀ ⊗ ℤ`
    let ⟨R, iR, iRM, l, pf⟩ ← liftRing M iM y iRM₀ l₀ pf₀ q(ℤ) iZ iMZ
    let _i' ← synthInstanceQ q(Ring $R)
    assumeInstancesCommute
    -- build the new list and proof
    let qneg : Q($R × $M) → Q($R × $M) := fun (p : Q($R × $M)) ↦ q((- Prod.fst $p, Prod.snd $p))
    pure ⟨R, iR, iRM, l.onFst qneg, (q(neg_eq_smulAndSum $pf):)⟩
  -- parse a scalar multiplication: `(s₀ : S) • y`
  | ~q(@HSMul.hSMul _ _ _ (@instHSMul $S _ $iS) $s₀ $y) =>
    let ⟨_, _, iRM₀, l₀, pf₀⟩ ← parse M iM y
    let i₁ ← synthInstanceQ q(Semiring $S)
    let i₂ ← synthInstanceQ q(Module $S $M)
    assumeInstancesCommute
    -- lift from original semiring of scalars (say `R₀`) to `R₀ ⊗ S`
    let ⟨R, iR, iRM, l, pf₂, s, pf₁⟩ ← matchRings' M iM y iRM₀ l₀ pf₀ i₁ i₂ s₀
    -- build the new list and proof
    let sl : List (Q($R × $M) × ℕ) := l.onFst (fun p ↦ q(($s * Prod.fst $p, Prod.snd $p)))
    pure ⟨R, iR, iRM, sl, (q((Eq.trans $pf₁ (smul_eq_smulAndSum $pf₂ $s))) :)⟩
  -- parse a `(0:M)`
  | ~q(0) => pure ⟨q(Nat), q(Nat.instSemiring), q(AddCommGroup.toNatModule), [], q(zero_pf $M)⟩
  -- anything else should be treated as an atom
  | _ =>
    let k : ℕ ← AtomM.addAtom x
    pure ⟨q(Nat), q(Nat.instSemiring), q(AddCommGroup.toNatModule), [(q((1, $x)), k)], q(one_pf $x)⟩

theorem eq_cons_cons {R : Type*} {M : Type*} [AddMonoid M] [Zero R] [SMul R M] {r₁ r₂ : R} (m : M)
    {l₁ l₂ : List (R × M)} (h1 : r₁ = r₂) (h2 : smulAndSum l₁ = smulAndSum l₂) :
      smulAndSum ((r₁, m) :: l₁) = smulAndSum ((r₂, m) :: l₂) := by
  simp only [smulAndSum] at *
  simp [h1, h2]

theorem eq_cons_const {R : Type*} {M : Type*} [AddCommMonoid M] [Semiring R] [Module R M] {r : R}
    (m : M) {n : M} {l : List (R × M)} (h1 : r = 0) (h2 : smulAndSum l = n) :
    smulAndSum ((r, m) :: l) = n := by
  simp only [smulAndSum] at *
  simp [h1, h2]

theorem eq_const_cons {R : Type*} {M : Type*} [AddCommMonoid M] [Semiring R] [Module R M] {r : R}
    (m : M) {n : M} {l : List (R × M)} (h1 : 0 = r) (h2 : n = smulAndSum l) :
    n = smulAndSum ((r, m) :: l) := by
  simp only [smulAndSum] at *
  simp [← h1, h2]

partial def reduceCoefficientwise {v : Level} {R : Q(Type)} {M : Q(Type v)}
    (iM : Q(AddCommMonoid $M)) (iR : Q(Semiring $R)) (iRM : Q(Module $R $M))
    (l₁ l₂ : List (Q($R × $M) × ℕ)) (g : MVarId) :
    MetaM (List MVarId) := do
  trace[debug] "creating goals to compare {l₁} and {l₂}"
  let _i ← synthInstanceQ q(Zero $R)
  let ll₁ : Q(List ($R × $M)) := (l₁.map Prod.fst).quote
  let ll₂ : Q(List ($R × $M)) := (l₂.map Prod.fst).quote
  trace[debug] "current goal is {← g.getType}"
  let t : Q(Prop) := q(smulAndSum $ll₁ = smulAndSum $ll₂)
  trace[debug] "checking that this is the same as {t} ..."
  trace[debug] "we'll be inspecting {← isDefEq (← g.getType).consumeMData t}"
  guard (← isDefEq (← g.getType).consumeMData t)
  trace[debug] "... ok"
  assumeInstancesCommute
  match l₁, l₂ with
  | [], [] =>
    trace[debug] "we've reached the bottom; goal is {g}"
    let pf : Q(smulAndSum $ll₁ = smulAndSum $ll₁) := q(rfl)
    g.assign pf
    trace[debug] "successfully resolved bottom goal with rfl"
    pure []
  | [], (e, _) :: L =>
    let mvar₁ : Q((0:$R) = Prod.fst $e) ← mkFreshExprMVar q((0:$R) = Prod.fst $e)
    let LL : Q(List ($R × $M)) := (L.map Prod.fst).quote
    let mvar₂ : Q((0:$M) = smulAndSum $LL) ← mkFreshExprMVar q((0:$M) = smulAndSum $LL)
    let mvars ← reduceCoefficientwise iM iR iRM [] L mvar₂.mvarId!
    g.assign q(eq_const_cons (Prod.snd $e) $mvar₁ $mvar₂)
    pure (mvar₁.mvarId! :: mvars)
  | (e, _) :: L, [] =>
    let mvar₁ : Q(Prod.fst $e = (0:$R)) ← mkFreshExprMVar q(Prod.fst $e = (0:$R))
    let LL : Q(List ($R × $M)) := (L.map Prod.fst).quote
    let mvar₂ : Q(smulAndSum $LL = (0:$M)) ← mkFreshExprMVar q(smulAndSum $LL = (0:$M))
    let mvars ← reduceCoefficientwise iM iR iRM L [] mvar₂.mvarId!
    g.assign q(eq_cons_const (Prod.snd $e) $mvar₁ $mvar₂)
    pure (mvar₁.mvarId! :: mvars)
  | (e₁, k₁) :: L₁, (e₂, k₂) :: L₂ =>
    let LL₁ : Q(List ($R × $M)) := (L₁.map Prod.fst).quote
    let LL₂ : Q(List ($R × $M)) := (L₂.map Prod.fst).quote
    if k₁ < k₂ then
      let mvar₁ : Q(Prod.fst $e₁ = (0:$R)) ← mkFreshExprMVar q(Prod.fst $e₁ = (0:$R))
      let mvar₂ : Q(smulAndSum $LL₁ = smulAndSum $ll₂)
        ← mkFreshExprMVar q(smulAndSum $LL₁ = smulAndSum $ll₂)
      let mvars ← reduceCoefficientwise iM iR iRM L₁ l₂ mvar₂.mvarId!
      g.assign q(eq_cons_const (Prod.snd $e₁) $mvar₁ $mvar₂)
      pure (mvar₁.mvarId! :: mvars)
    else if k₁ = k₂ then
      let mvar₁ : Q(Prod.fst $e₁ = Prod.fst $e₂) ← mkFreshExprMVar q(Prod.fst $e₁ = Prod.fst $e₂)
      let mvar₂ : Q(smulAndSum $LL₁ = smulAndSum $LL₂)
        ← mkFreshExprMVar q(smulAndSum $LL₁ = smulAndSum $LL₂)
      let mvars ← reduceCoefficientwise iM iR iRM L₁ L₂ mvar₂.mvarId!
      g.assign q(eq_cons_cons (Prod.snd $e₁) $mvar₁ $mvar₂)
      pure (mvar₁.mvarId! :: mvars)
    else
      let mvar₁ : Q((0:$R) = Prod.fst $e₂) ← mkFreshExprMVar q((0:$R) = Prod.fst $e₂)
      let mvar₂ : Q(smulAndSum $ll₁ = smulAndSum $LL₂)
        ← mkFreshExprMVar q(smulAndSum $ll₁ = smulAndSum $LL₂)
      let mvars ← reduceCoefficientwise iM iRM iR l₁ L₂ mvar₂.mvarId!
      g.assign q(eq_const_cons (Prod.snd $e₂) $mvar₁ $mvar₂)
      pure (mvar₁.mvarId! :: mvars)

def matchScalarsAux (g : MVarId) : AtomM (List MVarId) := do
  let eqData ← do
    match (← g.getType').eq? with
    | some e => pure e
    | none => throwError "goal {← g.getType} is not an equality"
  let .sort u ← whnf (← inferType eqData.1) | unreachable!
  let some v := u.dec | throwError "goal cannot be an equality in Sort"
  let ((M : Q(Type v)), (lhs : Q($M)), (rhs :Q($M))) := eqData
  let iM ← synthInstanceQ q(AddCommMonoid.{v} $M)
  trace[debug] "parsing LHS, {lhs}"
  let e₁ ← parse M iM lhs
  have R₁ : Q(Type) := e₁.fst
  trace[debug] "got back some stuff over the semiring {R₁}"
  have _iR₁ : Q(Semiring.{0} $R₁) := e₁.snd.fst
  let iRM₁ ← synthInstanceQ q(Module $R₁ $M)
  -- would be better to do the following, but doesn't work?
  -- have iRM₁ : Q(@Module.{0, v} $R₁ $M $_iR₁ $iM) := e.snd.snd.fst
  assumeInstancesCommute
  have l₁ : List (Q($R₁ × $M) × ℕ) := e₁.snd.snd.snd.fst
  let ll₁ : Q(List ($R₁ × $M)) := (List.map Prod.fst l₁).quote
  let pf₁ : Q($lhs = smulAndSum $ll₁) := e₁.snd.snd.snd.snd
  trace[debug] "unpacked the LHS parse successfully"
  trace[debug] "parsing RHS, {rhs}"
  let e₂ ← parse M iM rhs
  have R₂ : Q(Type) := e₂.fst
  have _iR₂ : Q(Semiring.{0} $R₂) := e₂.snd.fst
  let iRM₂ ← synthInstanceQ q(Module $R₂ $M)
  have l₂ : List (Q($R₁ × $M) × ℕ) := e₂.snd.snd.snd.fst
  let ll₂ : Q(List ($R₁ × $M)) := (List.map Prod.fst l₂).quote
  let pf₂ : Q($rhs = smulAndSum $ll₂) := e₂.snd.snd.snd.snd
  trace[debug] "unpacked the RHS parse successfully"
  -- lift LHS and RHS to same scalar ring
  let ⟨R, iR, iRM, l₁', l₂', pf₁', pf₂'⟩ ← matchRings M iM lhs rhs iRM₁ l₁ pf₁ iRM₂ l₂ pf₂
  -- start to rig up the collection of goals we will reduce to
  let ll₁' : Q(List ($R × $M)) := (l₁'.map Prod.fst).quote
  let ll₂' : Q(List ($R × $M)) := (l₂'.map Prod.fst).quote
  let mvar : Q(smulAndSum $ll₁' = smulAndSum $ll₂')
    ← mkFreshExprMVar q(smulAndSum $ll₁' = smulAndSum $ll₂')
  g.assign q(Eq.trans (Eq.trans $pf₁' $mvar) (Eq.symm $pf₂'))
  reduceCoefficientwise iM iR iRM l₁' l₂' mvar.mvarId!

def matchScalars (g : MVarId) : MetaM (List MVarId) := AtomM.run .default (matchScalarsAux g)

/- Do we also want to import `Mathlib.Data.Complex.Module`, so that the `ℝ`-to-`ℂ` algebra map can
be added to the list of algebra-maps which get special-cased here?  (The lemma would be
`Complex.coe_algebraMap`.)-/

elab "match_scalars" : tactic => Tactic.withMainContext <| Tactic.focus do
  Tactic.liftMetaTactic matchScalars
  Tactic.allGoals <|
    Tactic.evalTactic <|
      ← `(tactic | push_cast [eq_natCast, eq_intCast, eq_ratCast, -Int.reduceAdd, -Int.reduceNeg,
        -Int.reduceEq, -Nat.reduceAdd])

elab "module" : tactic => Tactic.withMainContext <| Tactic.focus do
  Tactic.liftMetaTactic matchScalars
  Tactic.allGoals <| do
    Tactic.evalTactic <|
      ← `(tactic | (push_cast [eq_natCast, eq_intCast, eq_ratCast, -Int.reduceAdd, -Int.reduceNeg,
        -Int.reduceEq, -Nat.reduceAdd]; try ring1))
  Tactic.done
