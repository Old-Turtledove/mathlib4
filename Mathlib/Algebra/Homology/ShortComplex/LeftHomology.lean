/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.Algebra.Homology.ShortComplex.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-! LeftHomology of short complexes

Given a short complex `S : ShortComplex C`, which consists of two composable
maps `f : X₁ ⟶ X₂` and `g : X₂ ⟶ X₃` such that `f ≫ g = 0`, we shall define
here the "left homology" `S.leftHomology` of `S` (TODO). For this, we introduce the
notion of "left homology data". Such an `h : S.LeftHomologyData` consists of the
datum of morphisms `i : K ⟶ X₂` and `π : K ⟶ H` such that `i` identifies
`K` to the kernel of `g : X₂ ⟶ X₃`, and that `π` identifies `H` to the cokernel
of the induced map `f' : X₁ ⟶ K`.

TODO: When such a `S.LeftHomologyData` exists, we shall say that `[S.HasLeftHomology]`
and we define `S.leftHomology` to be the `H` field of a chosen left homology data.
Similarly, we shall define `S.cycles` to be the `K` field.

The dual notion is defined in `RightHomologyData.lean`. In `Homology.lean`,
when `S` has two compatible left and right homology data (i.e. they give
the same `H` up to a canonical isomorphism), we shall define `[S.HasHomology]`
and `S.homology` (TODO).

-/

open ZeroObject

namespace CategoryTheory

open Category

namespace Limits

variable {C : Type _} [Category C] [HasZeroMorphisms C]

/-- `X` identifies to the kernel of a zero map `X ⟶ Y`. -/
def KernelFork.IsLimit.ofId {X Y : C} (f : X ⟶ Y) (hf : f = 0) :
    IsLimit (KernelFork.ofι (𝟙 X) (show 𝟙 X ≫ f = 0 by rw [hf, comp_zero])) :=
  KernelFork.IsLimit.ofι _ _ (fun x _ => x) (fun _ _ => comp_id _)
    (fun _ _ _ hb => by simp only [← hb, comp_id])

/-- Any zero object identifies to the kernel of a given monomorphisms. -/
def KernelFork.IsLimit.ofIsZeroOfMono {X Y : C} {f : X ⟶ Y} (c : KernelFork f)
    (hf : Mono f) (h : IsZero c.pt) : IsLimit c :=
  isLimitAux _ (fun s => 0) (fun s => by rw [zero_comp, ← cancel_mono f, zero_comp, s.condition])
    (fun _ _ _ => h.eq_of_tgt _ _)

lemma KernelFork.IsLimit.isIso_ι_of_zero {X Y : C} {f : X ⟶ Y} (c : KernelFork f)
    (hc : IsLimit c) (hf : f = 0) : IsIso c.ι := by
  let e : c.pt ≅ X := IsLimit.conePointUniqueUpToIso hc
    (KernelFork.IsLimit.ofId (f : X ⟶ Y) hf)
  have eq : e.inv ≫ c.ι = 𝟙 X := Fork.IsLimit.lift_ι hc
  haveI : IsIso (e.inv ≫ c.ι) := by
    rw [eq]
    infer_instance
  exact IsIso.of_isIso_comp_left e.inv c.ι

/-- `Y` identifies to the cokernel of a zero map `X ⟶ Y`. -/
def CokernelCofork.IsColimit.ofId {X Y : C} (f : X ⟶ Y) (hf : f = 0) :
    IsColimit (CokernelCofork.ofπ (𝟙 Y) (show f ≫ 𝟙 Y = 0 by rw [hf, zero_comp])) :=
  CokernelCofork.IsColimit.ofπ  _ _ (fun x _ => x) (fun _ _ => id_comp _)
    (fun _ _ _ hb => by simp only [← hb, id_comp])

/-- Any zero object identifies to the cokernel of a given epimorphisms. -/
def CokernelCofork.IsColimit.ofIsZeroOfEpi {X Y : C} {f : X ⟶ Y} (c : CokernelCofork f)
    (hf : Epi f) (h : IsZero c.pt) : IsColimit c :=
  isColimitAux _ (fun s => 0) (fun s => by rw [comp_zero, ← cancel_epi f, comp_zero, s.condition])
    (fun _ _ _ => h.eq_of_src _ _)

lemma CokernelCofork.IsColimit.isIso_π_of_zero {X Y : C} {f : X ⟶ Y} (c : CokernelCofork f)
    (hc : IsColimit c) (hf : f = 0) : IsIso c.π := by
  let e : c.pt ≅ Y := IsColimit.coconePointUniqueUpToIso hc
    (CokernelCofork.IsColimit.ofId (f : X ⟶ Y) hf)
  have eq : c.π ≫ e.hom = 𝟙 Y := Cofork.IsColimit.π_desc hc
  haveI : IsIso (c.π ≫ e.hom) := by
    rw [eq]
    dsimp
    infer_instance
  exact IsIso.of_isIso_comp_right c.π e.hom

/-- a colimit cokernel cofork gives a limit kernel fork in the opposite category -/
def CokernelCofork.IsColimit.ofπOp {X Y Q : C} (p : Y ⟶ Q) {f : X ⟶ Y}
    (w : f ≫ p = 0) (h : IsColimit (CokernelCofork.ofπ p w)) :
    IsLimit (KernelFork.ofι p.op (show p.op ≫ f.op = 0 by rw [← op_comp, w, op_zero])) :=
  KernelFork.IsLimit.ofι _ _
    (fun x hx => (h.desc (CokernelCofork.ofπ x.unop (Quiver.Hom.op_inj hx))).op)
    (fun x hx => Quiver.Hom.unop_inj (Cofork.IsColimit.π_desc h))
    (fun x hx b hb => Quiver.Hom.unop_inj (Cofork.IsColimit.hom_ext h
      (by simpa only [Quiver.Hom.unop_op, Cofork.IsColimit.π_desc] using Quiver.Hom.op_inj hb)))

/-- a colimit cokernel cofork in the opposite category gives a limit kernel fork
in the original category -/
def CokernelCofork.IsColimit.ofπUnop {X Y Q : Cᵒᵖ} (p : Y ⟶ Q) {f : X ⟶ Y}
    (w : f ≫ p = 0) (h : IsColimit (CokernelCofork.ofπ p w)) :
    IsLimit (KernelFork.ofι p.unop (show p.unop ≫ f.unop = 0 by rw [← unop_comp, w, unop_zero])) :=
  KernelFork.IsLimit.ofι _ _
    (fun x hx => (h.desc (CokernelCofork.ofπ x.op (Quiver.Hom.unop_inj hx))).unop)
    (fun x hx => Quiver.Hom.op_inj (Cofork.IsColimit.π_desc h))
    (fun x hx b hb => Quiver.Hom.op_inj (Cofork.IsColimit.hom_ext h
      (by simpa only [Quiver.Hom.op_unop, Cofork.IsColimit.π_desc] using Quiver.Hom.unop_inj hb)))

/-- a limit kernel fork gives a colimit cokernel cofork in the opposite category -/
def KernelFork.IsLimit.ofιOp {K X Y : C} (i : K ⟶ X) {f : X ⟶ Y}
    (w : i ≫ f = 0) (h : IsLimit (KernelFork.ofι i w)) :
    IsColimit (CokernelCofork.ofπ i.op
      (show f.op ≫ i.op = 0 by rw [← op_comp, w, op_zero])) :=
  CokernelCofork.IsColimit.ofπ _ _
    (fun x hx => (h.lift (KernelFork.ofι x.unop (Quiver.Hom.op_inj hx))).op)
    (fun x hx => Quiver.Hom.unop_inj (Fork.IsLimit.lift_ι h))
    (fun x hx b hb => Quiver.Hom.unop_inj (Fork.IsLimit.hom_ext h (by
      simpa only [Quiver.Hom.unop_op, Fork.IsLimit.lift_ι] using Quiver.Hom.op_inj hb)))

/-- a limit kernel fork in the opposite category gives a colimit cokernel cofork
in the original category -/
def KernelFork.IsLimit.ofιUnop {K X Y : Cᵒᵖ} (i : K ⟶ X) {f : X ⟶ Y}
    (w : i ≫ f = 0) (h : IsLimit (KernelFork.ofι i w)) :
    IsColimit (CokernelCofork.ofπ i.unop
      (show f.unop ≫ i.unop = 0 by rw [← unop_comp, w, unop_zero])) :=
  CokernelCofork.IsColimit.ofπ _ _
    (fun x hx => (h.lift (KernelFork.ofι x.op (Quiver.Hom.unop_inj hx))).unop)
    (fun x hx => Quiver.Hom.op_inj (Fork.IsLimit.lift_ι h))
    (fun x hx b hb => Quiver.Hom.op_inj (Fork.IsLimit.hom_ext h (by
      simpa only [Quiver.Hom.op_unop, Fork.IsLimit.lift_ι] using Quiver.Hom.unop_inj hb)))

end Limits

end CategoryTheory

namespace CategoryTheory

open Category Limits

namespace ShortComplex

variable {C D : Type _} [Category C] [Category D]
  [HasZeroMorphisms C]
  (S : ShortComplex C) {S₁ S₂ S₃ : ShortComplex C}

/-- A left homology data for a short complex `S` consists of morphisms `i : K ⟶ S.X₂` and
`π : K ⟶ H` such that `i` identifies `K` to the kernel of `g : S.X₂ ⟶ S.X₃`,
and that `π` identifies `H` to the cokernel of the induced map `f' : S.X₁ ⟶ K` --/
structure LeftHomologyData where
  /-- a choice of kernel of `S.g : S.X₂ ⟶ S.X₃`-/
  K : C
  /-- a choice of cokernel of the induced morphism `S.f' : S.X₁ ⟶ K`-/
  H : C
  /-- the inclusion of cycles in `S.X₂` -/
  i : K ⟶ S.X₂
  /-- the projection from cycles to the (left) homology -/
  π : K ⟶ H
  /-- the kernel condition for `i` -/
  wi : i ≫ S.g = 0
  /-- `i : K ⟶ S.X₂ ` is a kernel of `g : S.X₂ ⟶ S.X₃` -/
  hi : IsLimit (KernelFork.ofι i wi)
  /-- the cokernel condition for `π` -/
  wπ : hi.lift (KernelFork.ofι _ S.zero) ≫ π = 0
  /-- `π : K ⟶ H ` is a cokernel of the induced morphism `S.f' : S.X₁ ⟶ K` -/
  hπ : IsColimit (CokernelCofork.ofπ π wπ)

initialize_simps_projections LeftHomologyData (-hi, -hπ)

namespace LeftHomologyData

/-- the chosen kernels and cokernels of the limits API gives a `S.LeftHomologyData` -/
@[simps]
noncomputable def ofKerOfCoker [HasKernel S.g] [HasCokernel (kernel.lift S.g S.f S.zero)] :
  S.LeftHomologyData :=
{ K := kernel S.g,
  H := cokernel (kernel.lift S.g S.f S.zero),
  i := kernel.ι _,
  π := cokernel.π _,
  wi := kernel.condition _,
  hi := kernelIsKernel _,
  wπ := cokernel.condition _,
  hπ := cokernelIsCokernel _, }

attribute [reassoc (attr := simp)] wi wπ

variable {S}
variable (h : S.LeftHomologyData) {A : C}

instance : Mono h.i :=
  ⟨fun _ _ => Fork.IsLimit.hom_ext h.hi⟩

instance : Epi h.π :=
  ⟨fun _ _ => Cofork.IsColimit.hom_ext h.hπ⟩

/-- any morphism `k : A ⟶ S.X₂` that is a cycle (i.e. `k ≫ S.g = 0`) lifts to a morphism `A ⟶ K` -/
def liftK (k : A ⟶ S.X₂) (hk : k ≫ S.g = 0) : A ⟶ h.K :=
h.hi.lift (KernelFork.ofι k hk)

@[reassoc (attr := simp)]
lemma liftK_i (k : A ⟶ S.X₂) (hk : k ≫ S.g = 0) :
  h.liftK k hk ≫ h.i = k :=
h.hi.fac _ WalkingParallelPair.zero

/-- the (left) homology class `A ⟶ H` attached to a cycle `k : A ⟶ S.X₂` -/
@[simp]
def liftH (k : A ⟶ S.X₂) (hk : k ≫ S.g = 0) : A ⟶ h.H :=
  h.liftK k hk ≫ h.π

/-- The morphism `S.X₁ ⟶ h.K` induced by `S.f : S.X₁ ⟶ S.X₂` and the fact that
`h.K` is a kernel of `S.g : S.X₂ ⟶ S.X₃`. -/
def f' : S.X₁ ⟶ h.K := h.liftK S.f S.zero

@[reassoc (attr := simp)]
lemma f'_i : h.f' ≫ h.i = S.f :=
liftK_i _ _ _

@[reassoc (attr := simp)]
lemma f'_π : h.f' ≫ h.π = 0 := h.wπ

@[reassoc]
lemma liftK_π_eq_zero_of_boundary (k : A ⟶ S.X₂) (x : A ⟶ S.X₁) (hx : k = x ≫ S.f) :
    h.liftK k (by rw [hx, assoc, S.zero, comp_zero]) ≫ h.π = 0 := by
  rw [show 0 = (x ≫ h.f') ≫ h.π by simp]
  congr 1
  simp only [← cancel_mono h.i, hx, liftK_i, assoc, f'_i]

/-- For `h : S.LeftHomologyData`, this is a restatement of `h.hπ`, saying that
`π : h.K ⟶ h.H` is a cokernel of `h.f' : S.X₁ ⟶ h.K`. -/
def hπ' : IsColimit (CokernelCofork.ofπ h.π h.f'_π) := h.hπ

/-- the morphism `H ⟶ A` induced by a morphism `k : K ⟶ A` such that `f' ≫ k = 0` -/
def descH (k : h.K ⟶ A) (hk : h.f' ≫ k = 0) :
  h.H ⟶ A :=
h.hπ.desc (CokernelCofork.ofπ k hk)

@[reassoc (attr := simp)]
lemma π_descH (k : h.K ⟶ A) (hk : h.f' ≫ k = 0) :
  h.π ≫ h.descH k hk = k :=
h.hπ.fac (CokernelCofork.ofπ k hk) WalkingParallelPair.one

variable (S)

/-- When the second map `S.g` is zero, this is the left homology data on `S` given
by any colimit cokernel cofork of `S.f` -/
@[simps]
def ofIsColimitCokernelCofork (hg : S.g = 0) (c : CokernelCofork S.f) (hc : IsColimit c) :
  S.LeftHomologyData where
  K := S.X₂
  H := c.pt
  i := 𝟙 _
  π := c.π
  wi := by rw [id_comp, hg]
  hi := KernelFork.IsLimit.ofId _ hg
  wπ := CokernelCofork.condition _
  hπ := IsColimit.ofIsoColimit hc (Cofork.ext (Iso.refl _) (by aesop_cat))

@[simp] lemma ofIsColimitCokernelCofork_f' (hg : S.g = 0) (c : CokernelCofork S.f)
    (hc : IsColimit c) : (ofIsColimitCokernelCofork S hg c hc).f' = S.f := by
  rw [← cancel_mono (ofIsColimitCokernelCofork S hg c hc).i, f'_i,
    ofIsColimitCokernelCofork_i]
  dsimp
  rw [comp_id]

/-- When the second map `S.g` is zero, this is the left homology data on `S` given by
the chosen `cokernel S.f` -/
@[simps!]
noncomputable def ofHasCokernel [HasCokernel S.f] (hg : S.g = 0) : S.LeftHomologyData :=
  ofIsColimitCokernelCofork S hg _ (cokernelIsCokernel _)

/-- When the first map `S.f` is zero, this is the left homology data on `S` given
by any limit kernel fork of `S.g` -/
@[simps]
def ofIsLimitKernelFork (hf : S.f = 0) (c : KernelFork S.g) (hc : IsLimit c) :
  S.LeftHomologyData where
  K := c.pt
  H := c.pt
  i := c.ι
  π := 𝟙 _
  wi := KernelFork.condition _
  hi := IsLimit.ofIsoLimit hc (Fork.ext (Iso.refl _) (by aesop_cat))
  wπ := Fork.IsLimit.hom_ext hc (by
    dsimp
    simp only [comp_id, zero_comp, Fork.IsLimit.lift_ι, Fork.ι_ofι, hf])
  hπ := CokernelCofork.IsColimit.ofId _ (Fork.IsLimit.hom_ext hc (by
    dsimp
    simp only [comp_id, zero_comp, Fork.IsLimit.lift_ι, Fork.ι_ofι, hf]))

@[simp] lemma ofIsLimitKernelFork_f' (hf : S.f = 0) (c : KernelFork S.g)
  (hc : IsLimit c) : (ofIsLimitKernelFork S hf c hc).f' = 0 :=
by rw [← cancel_mono (ofIsLimitKernelFork S hf c hc).i, f'_i, hf, zero_comp]

/-- When the first map `S.f` is zero, this is the left homology data on `S` given
by chosen `kernel S.g` -/
@[simp]
noncomputable def ofHasKernel [HasKernel S.g] (hf : S.f = 0) : S.LeftHomologyData :=
  ofIsLimitKernelFork S hf _ (kernelIsKernel _)

/-- When both `S.f` and `S.g` are zero, the middle object `S.X₂` gives a left homology data on S -/
@[simps]
def ofZeros (hf : S.f = 0) (hg : S.g = 0) : S.LeftHomologyData where
  K := S.X₂
  H := S.X₂
  i := 𝟙 _
  π := 𝟙 _
  wi := by rw [id_comp, hg]
  hi := KernelFork.IsLimit.ofId _ hg
  wπ := by
    change S.f ≫ 𝟙 _ = 0
    simp only [hf, zero_comp]
  hπ := CokernelCofork.IsColimit.ofId _ hf

@[simp]
lemma ofZeros_f' (hf : S.f = 0) (hg : S.g = 0) :
    (ofZeros S hf hg).f' = 0 := by
  rw [← cancel_mono ((ofZeros S hf hg).i), zero_comp, f'_i, hf]

/-- the obvious left homology data of the short complex `c.pt ⟶ X ⟶ Y` when `c` is a limit
kernel fork of the morphism `f : X ⟶ Y`. -/
@[simps]
noncomputable def kernelSequence' {X Y : C} (f : X ⟶ Y) (c : KernelFork f) (hc : IsLimit c)
    [HasZeroObject C] :
    LeftHomologyData (ShortComplex.mk c.ι f (KernelFork.condition c)) where
  K := c.pt
  H := 0
  i := c.ι
  π := 0
  wi := KernelFork.condition _
  hi := IsLimit.ofIsoLimit hc (Fork.ext (Iso.refl _) (by simp))
  wπ := Subsingleton.elim _ _
  hπ := by
    refine' CokernelCofork.IsColimit.ofIsZeroOfEpi _ _ _
    . dsimp
      convert (inferInstance : Epi (𝟙 c.pt))
      haveI := mono_of_isLimit_fork hc
      rw [← cancel_mono c.ι]
      simp only [Fork.ofι_pt, parallelPair_obj_zero, Functor.const_obj_obj,
        Fork.IsLimit.lift_ι, Fork.ι_ofι, id_comp, comp_id]
    . apply isZero_zero

/-- for any morphism `f : X ⟶ Y`, this is the obvious left homology data of the short
complex `kernel f ⟶ X ⟶ Y`. -/
@[simps!]
noncomputable def kernelSequence {X Y : C} (f : X ⟶ Y) [HasKernel f] [HasZeroObject C] :
    LeftHomologyData (ShortComplex.mk (kernel.ι f) f (kernel.condition f)) := by
  let h := kernelSequence' f _ (kernelIsKernel f)
  exact h

end LeftHomologyData

class HasLeftHomology : Prop :=
(condition : Nonempty S.LeftHomologyData)

noncomputable def leftHomologyData [HasLeftHomology S] :
  S.LeftHomologyData := HasLeftHomology.condition.some

variable {S}

namespace HasLeftHomology

lemma mk' (h : S.LeftHomologyData) : HasLeftHomology S :=
⟨Nonempty.intro h⟩

instance of_ker_of_coker
    [HasKernel S.g] [HasCokernel (kernel.lift S.g S.f S.zero)] :
  S.HasLeftHomology := HasLeftHomology.mk' (LeftHomologyData.ofKerOfCoker S)

instance of_hasCokernel {X Y : C} (f : X ⟶ Y) (Z : C) [HasCokernel f] :
    (ShortComplex.mk f (0 : Y ⟶ Z) comp_zero).HasLeftHomology :=
  HasLeftHomology.mk' (LeftHomologyData.ofHasCokernel _ rfl)

instance of_hasKernel {Y Z : C} (g : Y ⟶ Z) (X : C) [HasKernel g] :
    (ShortComplex.mk (0 : X ⟶ Y) g zero_comp).HasLeftHomology :=
  HasLeftHomology.mk' (LeftHomologyData.ofHasKernel _ rfl)

instance of_zeros (X Y Z : C) :
    (ShortComplex.mk (0 : X ⟶ Y) (0 : Y ⟶ Z) zero_comp).HasLeftHomology :=
  HasLeftHomology.mk' (LeftHomologyData.ofZeros _ rfl rfl)

end HasLeftHomology

section

variable (φ : S₁ ⟶ S₂) (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData)

structure LeftHomologyMapData where
  φK : h₁.K ⟶ h₂.K
  φH : h₁.H ⟶ h₂.H
  commi : φK ≫ h₂.i = h₁.i ≫ φ.τ₂ := by aesop_cat
  commf' : h₁.f' ≫ φK = φ.τ₁ ≫ h₂.f' := by aesop_cat
  commπ : h₁.π ≫ φH = φK ≫ h₂.π := by aesop_cat

namespace LeftHomologyMapData

attribute [reassoc (attr := simp)] commi commf' commπ
attribute [nolint simpNF] mk.injEq

@[simps]
def zero (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData) :
  LeftHomologyMapData 0 h₁ h₂ where
  φK := 0
  φH := 0

@[simps]
def id (h : S.LeftHomologyData) : LeftHomologyMapData (𝟙 S) h h where
  φK := 𝟙 _
  φH := 𝟙 _

@[simps]
def comp {φ : S₁ ⟶ S₂} {φ' : S₂ ⟶ S₃} {h₁ : S₁.LeftHomologyData}
  {h₂ : S₂.LeftHomologyData} {h₃ : S₃.LeftHomologyData}
  (ψ : LeftHomologyMapData φ h₁ h₂) (ψ' : LeftHomologyMapData φ' h₂ h₃) :
  LeftHomologyMapData (φ ≫ φ') h₁ h₃ :=
{ φK := ψ.φK ≫ ψ'.φK,
  φH := ψ.φH ≫ ψ'.φH, }

instance : Subsingleton (LeftHomologyMapData φ h₁ h₂) :=
  ⟨fun ψ₁ ψ₂ => by
    have hK : ψ₁.φK = ψ₂.φK := by rw [← cancel_mono h₂.i, commi, commi]
    have hH : ψ₁.φH = ψ₂.φH := by rw [← cancel_epi h₁.π, commπ, commπ, hK]
    cases ψ₁
    cases ψ₂
    congr⟩

attribute [-simp] mk.injEq

instance : Inhabited (LeftHomologyMapData φ h₁ h₂) := ⟨by
  let φK : h₁.K ⟶ h₂.K := h₂.liftK (h₁.i ≫ φ.τ₂)
    (by rw [assoc, φ.comm₂₃, h₁.wi_assoc, zero_comp])
  have commf' : h₁.f' ≫ φK = φ.τ₁ ≫ h₂.f' := by
    rw [← cancel_mono h₂.i, assoc, assoc, LeftHomologyData.liftK_i,
      LeftHomologyData.f'_i_assoc, LeftHomologyData.f'_i, φ.comm₁₂]
  let φH : h₁.H ⟶ h₂.H := h₁.descH (φK ≫ h₂.π)
    (by rw [reassoc_of% commf', h₂.f'_π, comp_zero])
  exact ⟨φK, φH, by simp, commf', by simp⟩⟩

instance : Unique (LeftHomologyMapData φ h₁ h₂) := Unique.mk' _

def _root_.CategoryTheory.ShortComplex.leftHomologyMapData :
  LeftHomologyMapData φ h₁ h₂ := default

variable {φ h₁ h₂}

lemma congr_φH {γ₁ γ₂ : LeftHomologyMapData φ h₁ h₂} (eq : γ₁ = γ₂) : γ₁.φH = γ₂.φH := by rw [eq]
lemma congr_φK {γ₁ γ₂ : LeftHomologyMapData φ h₁ h₂} (eq : γ₁ = γ₂) : γ₁.φK = γ₂.φK := by rw [eq]

@[simps]
def ofZeros (φ : S₁ ⟶ S₂) (hf₁ : S₁.f = 0) (hg₁ : S₁.g = 0) (hf₂ : S₂.f = 0) (hg₂ : S₂.g = 0) :
  LeftHomologyMapData φ (LeftHomologyData.ofZeros S₁ hf₁ hg₁)
    (LeftHomologyData.ofZeros S₂ hf₂ hg₂) where
  φK := φ.τ₂
  φH := φ.τ₂

@[simps]
def ofIsColimitCokernelCofork (φ : S₁ ⟶ S₂)
  (hg₁ : S₁.g = 0) (c₁ : CokernelCofork S₁.f) (hc₁ : IsColimit c₁)
  (hg₂ : S₂.g = 0) (c₂ : CokernelCofork S₂.f) (hc₂ : IsColimit c₂) (f : c₁.pt ⟶ c₂.pt)
  (comm : φ.τ₂ ≫ c₂.π = c₁.π ≫ f) :
  LeftHomologyMapData φ (LeftHomologyData.ofIsColimitCokernelCofork S₁ hg₁ c₁ hc₁)
    (LeftHomologyData.ofIsColimitCokernelCofork S₂ hg₂ c₂ hc₂) where
  φK := φ.τ₂
  φH := f
  commπ := comm.symm
  commf' := by simp only [LeftHomologyData.ofIsColimitCokernelCofork_f', φ.comm₁₂]

@[simps]
def ofIsLimitKernelFork (φ : S₁ ⟶ S₂)
  (hf₁ : S₁.f = 0) (c₁ : KernelFork S₁.g) (hc₁ : IsLimit c₁)
  (hf₂ : S₂.f = 0) (c₂ : KernelFork S₂.g) (hc₂ : IsLimit c₂) (f : c₁.pt ⟶ c₂.pt)
  (comm : c₁.ι ≫ φ.τ₂ = f ≫ c₂.ι) :
  LeftHomologyMapData φ (LeftHomologyData.ofIsLimitKernelFork S₁ hf₁ c₁ hc₁)
    (LeftHomologyData.ofIsLimitKernelFork S₂ hf₂ c₂ hc₂) where
  φK := f
  φH := f
  commi := comm.symm

variable (S)

@[simps]
def compatibilityOfZerosOfIsColimitCokernelCofork (hf : S.f = 0) (hg : S.g = 0)
  (c : CokernelCofork S.f) (hc : IsColimit c) :
  LeftHomologyMapData (𝟙 S) (LeftHomologyData.ofZeros S hf hg)
    (LeftHomologyData.ofIsColimitCokernelCofork S hg c hc) where
  φK := 𝟙 _
  φH := c.π

@[simps]
def compatibilityOfZerosOfIsLimitKernelFork (hf : S.f = 0) (hg : S.g = 0)
  (c : KernelFork S.g) (hc : IsLimit c) :
  LeftHomologyMapData (𝟙 S)
    (LeftHomologyData.ofIsLimitKernelFork S hf c hc)
    (LeftHomologyData.ofZeros S hf hg) where
  φK := c.ι
  φH := c.ι

end LeftHomologyMapData

end

variable (S)

noncomputable def leftHomology [HasLeftHomology S] : C := S.leftHomologyData.H
noncomputable def cycles [HasLeftHomology S] : C := S.leftHomologyData.K
noncomputable def leftHomologyπ [HasLeftHomology S] : S.cycles ⟶ S.leftHomology :=
  S.leftHomologyData.π
noncomputable def iCycles [HasLeftHomology S] : S.cycles ⟶ S.X₂ := S.leftHomologyData.i
noncomputable def toCycles [HasLeftHomology S] : S.X₁ ⟶ S.cycles := S.leftHomologyData.f'

@[reassoc (attr := simp)]
lemma iCycles_g [HasLeftHomology S] : S.iCycles ≫ S.g = 0 :=
  S.leftHomologyData.wi

@[reassoc (attr := simp)]
lemma toCycles_i [HasLeftHomology S] : S.toCycles ≫ S.iCycles = S.f :=
  S.leftHomologyData.f'_i

instance [HasLeftHomology S] : Mono S.iCycles := by
  dsimp only [iCycles]
  infer_instance

instance [HasLeftHomology S] : Epi S.leftHomologyπ := by
  dsimp only [leftHomologyπ]
  infer_instance

variable {S}

def leftHomologyMap' (φ : S₁ ⟶ S₂) (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData) :
  h₁.H ⟶ h₂.H := (leftHomologyMapData φ _ _).φH

def cyclesMap' (φ : S₁ ⟶ S₂) (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData) :
  h₁.K ⟶ h₂.K := (leftHomologyMapData φ _ _).φK

@[reassoc (attr := simp)]
lemma cyclesMap'_i (φ : S₁ ⟶ S₂) (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData) :
    cyclesMap' φ h₁ h₂ ≫ h₂.i = h₁.i ≫ φ.τ₂ :=
  LeftHomologyMapData.commi _

@[reassoc (attr := simp)]
lemma f'_cyclesMap' (φ : S₁ ⟶ S₂) (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData) :
    h₁.f' ≫ cyclesMap' φ h₁ h₂ = φ.τ₁ ≫ h₂.f' := by
  simp only [← cancel_mono h₂.i, assoc, φ.comm₁₂, cyclesMap'_i,
    LeftHomologyData.f'_i_assoc, LeftHomologyData.f'_i]

@[reassoc (attr := simp)]
lemma leftHomologyπ_naturality' (φ : S₁ ⟶ S₂)
    (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData) :
    h₁.π ≫ leftHomologyMap' φ h₁ h₂ = cyclesMap' φ h₁ h₂ ≫ h₂.π :=
  LeftHomologyMapData.commπ _

noncomputable def leftHomologyMap [HasLeftHomology S₁] [HasLeftHomology S₂]
    (φ : S₁ ⟶ S₂) : S₁.leftHomology ⟶ S₂.leftHomology :=
  leftHomologyMap' φ _ _

noncomputable def cyclesMap [HasLeftHomology S₁] [HasLeftHomology S₂]
    (φ : S₁ ⟶ S₂) : S₁.cycles ⟶ S₂.cycles :=
  cyclesMap' φ _ _

@[reassoc (attr := simp)]
lemma cyclesMap_i (φ : S₁ ⟶ S₂) [S₁.HasLeftHomology] [S₂.HasLeftHomology] :
    cyclesMap φ ≫ S₂.iCycles = S₁.iCycles ≫ φ.τ₂ :=
  cyclesMap'_i _ _ _

@[reassoc (attr := simp)]
lemma toCycles_naturality (φ : S₁ ⟶ S₂) [S₁.HasLeftHomology] [S₂.HasLeftHomology] :
    S₁.toCycles ≫ cyclesMap φ = φ.τ₁ ≫ S₂.toCycles :=
  f'_cyclesMap' _ _ _

@[reassoc (attr := simp)]
lemma leftHomologyπ_naturality [HasLeftHomology S₁] [HasLeftHomology S₂]
    (φ : S₁ ⟶ S₂) :
    S₁.leftHomologyπ ≫ leftHomologyMap φ = cyclesMap φ ≫ S₂.leftHomologyπ :=
  leftHomologyπ_naturality' _ _ _

namespace LeftHomologyMapData

variable {φ : S₁ ⟶ S₂} {h₁ : S₁.LeftHomologyData} {h₂ : S₂.LeftHomologyData}
  (γ : LeftHomologyMapData φ h₁ h₂)

lemma leftHomologyMap'_eq : leftHomologyMap' φ h₁ h₂ = γ.φH :=
  LeftHomologyMapData.congr_φH (Subsingleton.elim _ _)

lemma cyclesMap'_eq : cyclesMap' φ h₁ h₂ = γ.φK :=
  LeftHomologyMapData.congr_φK (Subsingleton.elim _ _)

end LeftHomologyMapData

@[simp]
lemma leftHomologyMap'_id (h : S.LeftHomologyData) :
    leftHomologyMap' (𝟙 S) h h = 𝟙 _ :=
  (LeftHomologyMapData.id h).leftHomologyMap'_eq

@[simp]
lemma cyclesMap'_id (h : S.LeftHomologyData) :
    cyclesMap' (𝟙 S) h h = 𝟙 _ :=
  (LeftHomologyMapData.id h).cyclesMap'_eq

variable (S)

@[simp]
lemma leftHomologyMap_id [HasLeftHomology S] :
    leftHomologyMap (𝟙 S) = 𝟙 _ :=
  leftHomologyMap'_id _

@[simp]
lemma cyclesMap_id [HasLeftHomology S] :
    cyclesMap (𝟙 S) = 𝟙 _ :=
  cyclesMap'_id _

@[simp]
lemma leftHomologyMap'_zero (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData) :
    leftHomologyMap' 0 h₁ h₂ = 0 :=
  (LeftHomologyMapData.zero h₁ h₂).leftHomologyMap'_eq

@[simp]
lemma cyclesMap'_zero (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData) :
    cyclesMap' 0 h₁ h₂ = 0 :=
  (LeftHomologyMapData.zero h₁ h₂).cyclesMap'_eq

variable (S₁ S₂)

@[simp]
lemma leftHomologyMap_zero [HasLeftHomology S₁] [HasLeftHomology S₂] :
    leftHomologyMap (0 : S₁ ⟶ S₂) = 0 :=
  leftHomologyMap'_zero _ _

@[simp]
lemma cyclesMap_zero [HasLeftHomology S₁] [HasLeftHomology S₂] :
  cyclesMap (0 : S₁ ⟶ S₂) = 0 :=
cyclesMap'_zero _ _

variable {S₁ S₂}

@[reassoc]
lemma leftHomologyMap'_comp (φ₁ : S₁ ⟶ S₂) (φ₂ : S₂ ⟶ S₃)
    (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData) (h₃ : S₃.LeftHomologyData) :
    leftHomologyMap' (φ₁ ≫ φ₂) h₁ h₃ = leftHomologyMap' φ₁ h₁ h₂ ≫
      leftHomologyMap' φ₂ h₂ h₃ := by
  let γ₁ := leftHomologyMapData φ₁ h₁ h₂
  let γ₂ := leftHomologyMapData φ₂ h₂ h₃
  rw [γ₁.leftHomologyMap'_eq, γ₂.leftHomologyMap'_eq, (γ₁.comp γ₂).leftHomologyMap'_eq,
    LeftHomologyMapData.comp_φH]

@[reassoc]
lemma cyclesMap'_comp (φ₁ : S₁ ⟶ S₂) (φ₂ : S₂ ⟶ S₃)
    (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData) (h₃ : S₃.LeftHomologyData) :
    cyclesMap' (φ₁ ≫ φ₂) h₁ h₃ = cyclesMap' φ₁ h₁ h₂ ≫ cyclesMap' φ₂ h₂ h₃ := by
  let γ₁ := leftHomologyMapData φ₁ h₁ h₂
  let γ₂ := leftHomologyMapData φ₂ h₂ h₃
  rw [γ₁.cyclesMap'_eq, γ₂.cyclesMap'_eq, (γ₁.comp γ₂).cyclesMap'_eq,
    LeftHomologyMapData.comp_φK]

@[reassoc]
lemma leftHomologyMap_comp [HasLeftHomology S₁] [HasLeftHomology S₂] [HasLeftHomology S₃]
    (φ₁ : S₁ ⟶ S₂) (φ₂ : S₂ ⟶ S₃) :
    leftHomologyMap (φ₁ ≫ φ₂) = leftHomologyMap φ₁ ≫ leftHomologyMap φ₂ :=
leftHomologyMap'_comp _ _ _ _ _

@[reassoc]
lemma cyclesMap_comp [HasLeftHomology S₁] [HasLeftHomology S₂] [HasLeftHomology S₃]
    (φ₁ : S₁ ⟶ S₂) (φ₂ : S₂ ⟶ S₃) :
    cyclesMap (φ₁ ≫ φ₂) = cyclesMap φ₁ ≫ cyclesMap φ₂ :=
  cyclesMap'_comp _ _ _ _ _

attribute [simp] leftHomologyMap_comp cyclesMap_comp

@[simps]
def leftHomologyMapIso' (e : S₁ ≅ S₂) (h₁ : S₁.LeftHomologyData)
    (h₂ : S₂.LeftHomologyData) : h₁.H ≅ h₂.H where
  hom := leftHomologyMap' e.hom h₁ h₂
  inv := leftHomologyMap' e.inv h₂ h₁
  hom_inv_id := by rw [← leftHomologyMap'_comp, e.hom_inv_id, leftHomologyMap'_id]
  inv_hom_id := by rw [← leftHomologyMap'_comp, e.inv_hom_id, leftHomologyMap'_id]

instance isIso_leftHomologyMap'_of_isIso (φ : S₁ ⟶ S₂) [IsIso φ]
    (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData) :
    IsIso (leftHomologyMap' φ h₁ h₂) :=
  (inferInstance : IsIso (leftHomologyMapIso' (asIso φ) h₁ h₂).hom)

@[simps]
def cyclesMapIso' (e : S₁ ≅ S₂) (h₁ : S₁.LeftHomologyData)
  (h₂ : S₂.LeftHomologyData) : h₁.K ≅ h₂.K where
  hom := cyclesMap' e.hom h₁ h₂
  inv := cyclesMap' e.inv h₂ h₁
  hom_inv_id := by rw [← cyclesMap'_comp, e.hom_inv_id, cyclesMap'_id]
  inv_hom_id := by rw [← cyclesMap'_comp, e.inv_hom_id, cyclesMap'_id]

instance isIso_cyclesMap'_of_isIso (φ : S₁ ⟶ S₂) [IsIso φ]
    (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData) :
    IsIso (cyclesMap' φ h₁ h₂) :=
  (inferInstance : IsIso (cyclesMapIso' (asIso φ) h₁ h₂).hom)

@[simps]
noncomputable def leftHomologyMapIso (e : S₁ ≅ S₂) [S₁.HasLeftHomology]
  [S₂.HasLeftHomology] : S₁.leftHomology ≅ S₂.leftHomology where
  hom := leftHomologyMap e.hom
  inv := leftHomologyMap e.inv
  hom_inv_id := by rw [← leftHomologyMap_comp, e.hom_inv_id, leftHomologyMap_id]
  inv_hom_id := by rw [← leftHomologyMap_comp, e.inv_hom_id, leftHomologyMap_id]

instance isIso_leftHomologyMap_of_iso (φ : S₁ ⟶ S₂) [IsIso φ] [S₁.HasLeftHomology]
    [S₂.HasLeftHomology] :
    IsIso (leftHomologyMap φ) :=
  (inferInstance : IsIso (leftHomologyMapIso (asIso φ)).hom)

@[simps]
noncomputable def cyclesMapIso (e : S₁ ≅ S₂) [S₁.HasLeftHomology]
    [S₂.HasLeftHomology] : S₁.cycles ≅ S₂.cycles where
  hom := cyclesMap e.hom
  inv := cyclesMap e.inv
  hom_inv_id := by rw [← cyclesMap_comp, e.hom_inv_id, cyclesMap_id]
  inv_hom_id := by rw [← cyclesMap_comp, e.inv_hom_id, cyclesMap_id]

instance isIso_cyclesMap_of_iso (φ : S₁ ⟶ S₂) [IsIso φ] [S₁.HasLeftHomology]
    [S₂.HasLeftHomology] : IsIso (cyclesMap φ) :=
  (inferInstance : IsIso (cyclesMapIso (asIso φ)).hom)

variable {S}

noncomputable def LeftHomologyData.leftHomologyIso (h : S.LeftHomologyData) [S.HasLeftHomology] :
  S.leftHomology ≅ h.H := leftHomologyMapIso' (Iso.refl _) _ _

noncomputable def LeftHomologyData.cyclesIso (h : S.LeftHomologyData) [S.HasLeftHomology] :
  S.cycles ≅ h.K := cyclesMapIso' (Iso.refl _) _ _

@[reassoc (attr := simp)]
lemma LeftHomologyData.cyclesIso_hom_comp_i (h : S.LeftHomologyData) [S.HasLeftHomology] :
    h.cyclesIso.hom ≫ h.i = S.iCycles := by
  dsimp [iCycles, LeftHomologyData.cyclesIso]
  simp only [cyclesMap'_i, id_τ₂, comp_id]

@[reassoc (attr := simp)]
lemma LeftHomologyData.cyclesIso_inv_comp_iCycles (h : S.LeftHomologyData)
    [S.HasLeftHomology] : h.cyclesIso.inv ≫ S.iCycles = h.i := by
  simp only [← h.cyclesIso_hom_comp_i, Iso.inv_hom_id_assoc]

namespace LeftHomologyMapData

variable {φ : S₁ ⟶ S₂} {h₁ : S₁.LeftHomologyData} {h₂ : S₂.LeftHomologyData}
  (γ : LeftHomologyMapData φ h₁ h₂)

lemma leftHomologyMap_eq [S₁.HasLeftHomology] [S₂.HasLeftHomology] :
    leftHomologyMap φ = h₁.leftHomologyIso.hom ≫ γ.φH ≫ h₂.leftHomologyIso.inv := by
  dsimp [LeftHomologyData.leftHomologyIso, leftHomologyMapIso']
  rw [← γ.leftHomologyMap'_eq, ← leftHomologyMap'_comp,
    ← leftHomologyMap'_comp, id_comp, comp_id]
  rfl

lemma cyclesMap_eq [S₁.HasLeftHomology] [S₂.HasLeftHomology] :
    cyclesMap φ = h₁.cyclesIso.hom ≫ γ.φK ≫ h₂.cyclesIso.inv := by
  dsimp [LeftHomologyData.cyclesIso, cyclesMapIso']
  rw [← γ.cyclesMap'_eq, ← cyclesMap'_comp, ← cyclesMap'_comp, id_comp, comp_id]
  rfl

lemma leftHomologyMap_comm [S₁.HasLeftHomology] [S₂.HasLeftHomology] :
    leftHomologyMap φ ≫ h₂.leftHomologyIso.hom = h₁.leftHomologyIso.hom ≫ γ.φH := by
  simp only [γ.leftHomologyMap_eq, assoc, Iso.inv_hom_id, comp_id]

lemma cyclesMap_comm [S₁.HasLeftHomology] [S₂.HasLeftHomology] :
    cyclesMap φ ≫ h₂.cyclesIso.hom = h₁.cyclesIso.hom ≫ γ.φK := by
  simp only [γ.cyclesMap_eq, assoc, Iso.inv_hom_id, comp_id]

end LeftHomologyMapData

section

variable (C)
variable [HasKernels C] [HasCokernels C]

@[simps]
noncomputable def leftHomologyFunctor :
    ShortComplex C ⥤ C where
  obj S := S.leftHomology
  map := leftHomologyMap

@[simps]
noncomputable def cyclesFunctor :
    ShortComplex C ⥤ C where
  obj S := S.cycles
  map := cyclesMap

@[simps]
noncomputable def leftHomologyπNatTrans :
    cyclesFunctor C ⟶ leftHomologyFunctor C where
  app S := leftHomologyπ S
  naturality := fun _ _ φ => (leftHomologyπ_naturality φ).symm

@[simps]
noncomputable def iCyclesNatTrans :
    cyclesFunctor C ⟶ ShortComplex.π₂ where
  app S := S.iCycles

@[simps]
noncomputable def toCyclesNatTrans :
    π₁ ⟶ cyclesFunctor C where
  app S := S.toCycles
  naturality := fun _ _  φ => (toCycles_naturality φ).symm

end

namespace LeftHomologyData

@[simps]
noncomputable def ofEpiOfIsIsoOfMono (φ : S₁ ⟶ S₂) (h : LeftHomologyData S₁)
  [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] : LeftHomologyData S₂ := by
  let i : h.K ⟶ S₂.X₂ := h.i ≫ φ.τ₂
  have wi : i ≫ S₂.g = 0 := by simp only [assoc, φ.comm₂₃, h.wi_assoc, zero_comp]
  have hi : IsLimit (KernelFork.ofι i wi) := KernelFork.IsLimit.ofι _ _
    (fun x hx => h.liftK (x ≫ inv φ.τ₂) (by rw [assoc, ← cancel_mono φ.τ₃, assoc,
      assoc, ← φ.comm₂₃, IsIso.inv_hom_id_assoc, hx, zero_comp]))
    (fun x hx => by simp) (fun x hx b hb => by
      dsimp
      rw [← cancel_mono h.i, ← cancel_mono φ.τ₂, assoc, assoc, liftK_i_assoc,
        assoc, IsIso.inv_hom_id, comp_id, hb])
  let f' := hi.lift (KernelFork.ofι S₂.f S₂.zero)
  have hf' : φ.τ₁ ≫ f' = h.f' := by
    have eq := @Fork.IsLimit.lift_ι _ _ _ _ _ _ _ ((KernelFork.ofι S₂.f S₂.zero)) hi
    simp only [Fork.ι_ofι] at eq
    rw [← cancel_mono h.i, ← cancel_mono φ.τ₂, assoc, assoc, eq, f'_i, φ.comm₁₂]
  have wπ : f' ≫ h.π = 0 := by
    rw [← cancel_epi φ.τ₁, comp_zero, reassoc_of% hf', h.f'_π]
  have hπ : IsColimit (CokernelCofork.ofπ h.π wπ) := CokernelCofork.IsColimit.ofπ _ _
    (fun x hx => h.descH x (by rw [← hf', assoc, hx, comp_zero]))
    (fun x hx => by simp) (fun x hx b hb => by rw [← cancel_epi h.π, π_descH, hb])
  exact ⟨h.K, h.H, i, h.π, wi, hi, wπ, hπ⟩

@[simp]
lemma ofEpiOfIsIsoOfMono_τ₁_f' (φ : S₁ ⟶ S₂) (h : LeftHomologyData S₁)
    [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] : φ.τ₁ ≫ (ofEpiOfIsIsoOfMono φ h).f' = h.f' := by
  rw [← cancel_mono (ofEpiOfIsIsoOfMono φ h).i, assoc, f'_i,
    ofEpiOfIsIsoOfMono_i, f'_i_assoc, φ.comm₁₂]

@[simps]
noncomputable def ofEpiOfIsIsoOfMono' (φ : S₁ ⟶ S₂) (h : LeftHomologyData S₂)
    [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] : LeftHomologyData S₁ := by
  let i : h.K ⟶ S₁.X₂ := h.i ≫ inv φ.τ₂
  have wi : i ≫ S₁.g = 0 := by
    rw [assoc, ← cancel_mono φ.τ₃, zero_comp, assoc, assoc, ← φ.comm₂₃,
      IsIso.inv_hom_id_assoc, h.wi]
  have hi : IsLimit (KernelFork.ofι i wi) := KernelFork.IsLimit.ofι _ _
    (fun x hx => h.liftK (x ≫ φ.τ₂)
      (by rw [assoc, φ.comm₂₃, reassoc_of% hx, zero_comp]))
    (fun x hx => by simp )
    (fun x hx b hb => by rw [← cancel_mono h.i, ← cancel_mono (inv φ.τ₂), assoc, assoc,
      hb, liftK_i_assoc, assoc, IsIso.hom_inv_id, comp_id])
  let f' := hi.lift (KernelFork.ofι S₁.f S₁.zero)
  have hf' : f' ≫ i = S₁.f := Fork.IsLimit.lift_ι _
  have hf'' : f' = φ.τ₁ ≫ h.f' := by
    rw [← cancel_mono h.i, ← cancel_mono (inv φ.τ₂), assoc, assoc, assoc, hf', f'_i_assoc,
      φ.comm₁₂_assoc, IsIso.hom_inv_id, comp_id]
  have wπ : f' ≫ h.π = 0 := by simp only [hf'', assoc, f'_π, comp_zero]
  have hπ : IsColimit (CokernelCofork.ofπ h.π wπ) := CokernelCofork.IsColimit.ofπ _ _
    (fun x hx => h.descH x (by rw [← cancel_epi φ.τ₁, ← reassoc_of% hf'', hx, comp_zero]))
    (fun x hx => π_descH _ _ _)
    (fun x hx b hx => by rw [← cancel_epi h.π, π_descH, hx])
  exact ⟨h.K, h.H, i, h.π, wi, hi, wπ, hπ⟩

@[simp]
lemma ofEpiOfIsIsoOfMono'_f' (φ : S₁ ⟶ S₂) (h : LeftHomologyData S₂)
    [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] :
  (ofEpiOfIsIsoOfMono' φ h).f' = φ.τ₁ ≫ h.f' :=
by rw [← cancel_mono (ofEpiOfIsIsoOfMono' φ h).i, f'_i, ofEpiOfIsIsoOfMono'_i,
    assoc, f'_i_assoc, φ.comm₁₂_assoc, IsIso.hom_inv_id, comp_id]

noncomputable def ofIso (e : S₁ ≅ S₂) (h₁ : LeftHomologyData S₁) : LeftHomologyData S₂ :=
  h₁.ofEpiOfIsIsoOfMono e.hom

end LeftHomologyData

lemma hasLeftHomology_of_epi_of_isIso_of_mono (φ : S₁ ⟶ S₂) [HasLeftHomology S₁]
    [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] : HasLeftHomology S₂ :=
  HasLeftHomology.mk' (LeftHomologyData.ofEpiOfIsIsoOfMono φ S₁.leftHomologyData)

lemma hasLeftHomology_of_epi_of_isIso_of_mono' (φ : S₁ ⟶ S₂) [HasLeftHomology S₂]
    [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] : HasLeftHomology S₁ :=
HasLeftHomology.mk' (LeftHomologyData.ofEpiOfIsIsoOfMono' φ S₂.leftHomologyData)

lemma hasLeftHomology_of_iso {S₁ S₂ : ShortComplex C}
    (e : S₁ ≅ S₂) [HasLeftHomology S₁] : HasLeftHomology S₂ :=
  hasLeftHomology_of_epi_of_isIso_of_mono e.hom

namespace LeftHomologyMapData

@[simps]
def ofEpiOfIsIsoOfMono (φ : S₁ ⟶ S₂) (h : LeftHomologyData S₁)
    [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] :
    LeftHomologyMapData φ h (LeftHomologyData.ofEpiOfIsIsoOfMono φ h) where
  φK := 𝟙 _
  φH := 𝟙 _

@[simps]
noncomputable def ofEpiOfIsIsoOfMono' (φ : S₁ ⟶ S₂) (h : LeftHomologyData S₂)
  [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] :
    LeftHomologyMapData φ (LeftHomologyData.ofEpiOfIsIsoOfMono' φ h) h where
  φK := 𝟙 _
  φH := 𝟙 _

end LeftHomologyMapData

instance (φ : S₁ ⟶ S₂) (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData)
    [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] :
    IsIso (leftHomologyMap' φ h₁ h₂) := by
  let h₂' := LeftHomologyData.ofEpiOfIsIsoOfMono φ h₁
  haveI : IsIso (leftHomologyMap' φ h₁ h₂') := by
    rw [(LeftHomologyMapData.ofEpiOfIsIsoOfMono φ h₁).leftHomologyMap'_eq]
    dsimp
    infer_instance
  have eq := leftHomologyMap'_comp φ (𝟙 S₂) h₁ h₂' h₂
  rw [comp_id] at eq
  rw [eq]
  infer_instance

instance (φ : S₁ ⟶ S₂) [S₁.HasLeftHomology] [S₂.HasLeftHomology]
    [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] :
    IsIso (leftHomologyMap φ) := by
  dsimp only [leftHomologyMap]
  infer_instance

section

variable (S) (h : LeftHomologyData S)
  {A : C} (k : A ⟶ S.X₂) (hk : k ≫ S.g = 0) [HasLeftHomology S]

noncomputable def liftCycles : A ⟶ S.cycles :=
  S.leftHomologyData.liftK k hk

@[reassoc (attr := simp)]
lemma liftCycles_i : S.liftCycles k hk ≫ S.iCycles = k :=
  LeftHomologyData.liftK_i _ k hk

@[reassoc]
lemma comp_liftCycles {A' : C} (α : A' ⟶ A) :
    α ≫ S.liftCycles k hk = S.liftCycles (α ≫ k) (by rw [assoc, hk, comp_zero]) := by
  simp only [← cancel_mono S.iCycles, assoc, liftCycles_i]

noncomputable def cyclesIsKernel : IsLimit (KernelFork.ofι S.iCycles S.iCycles_g) :=
  S.leftHomologyData.hi

lemma isIso_iCycles_of_zero (hg : S.g = 0) : IsIso (S.iCycles) :=
  KernelFork.IsLimit.isIso_ι_of_zero _ S.cyclesIsKernel hg

@[simps]
noncomputable def cyclesIsoKernel [HasKernel S.g] : S.cycles ≅ kernel S.g where
  hom := kernel.lift S.g S.iCycles (by simp)
  inv := S.liftCycles (kernel.ι S.g) (by simp)
  hom_inv_id := by simp only [←  cancel_mono S.iCycles, assoc, liftCycles_i,
    kernel.lift_ι, id_comp]
  inv_hom_id := by simp only [← cancel_mono (kernel.ι S.g), assoc, kernel.lift_ι,
    liftCycles_i, id_comp]

@[simp]
noncomputable def liftLeftHomology : A ⟶ S.leftHomology :=
  S.liftCycles k hk ≫ S.leftHomologyπ

@[reassoc]
lemma liftCycles_leftHomologyπ_eq_zero_of_boundary (x : A ⟶ S.X₁) (hx : k = x ≫ S.f) :
    S.liftCycles k (by rw [hx, assoc, S.zero, comp_zero]) ≫ S.leftHomologyπ = 0 :=
  LeftHomologyData.liftK_π_eq_zero_of_boundary _ k x hx

@[reassoc (attr := simp)]
lemma toCycles_comp_leftHomology_π :
  S.toCycles ≫ S.leftHomologyπ = 0 :=
S.liftCycles_leftHomologyπ_eq_zero_of_boundary S.f (𝟙 _) (by rw [id_comp])

noncomputable def leftHomologyIsCokernel :
    IsColimit (CokernelCofork.ofπ S.leftHomologyπ S.toCycles_comp_leftHomology_π) :=
  S.leftHomologyData.hπ

@[reassoc (attr := simp)]
lemma liftCycles_comp_cyclesMap (φ : S ⟶ S₁) [S₁.HasLeftHomology] :
    S.liftCycles k hk ≫ cyclesMap φ =
      S₁.liftCycles (k ≫ φ.τ₂) (by rw [assoc, φ.comm₂₃, reassoc_of% hk, zero_comp]) := by
  simp only [← cancel_mono (S₁.iCycles), assoc, cyclesMap_i, liftCycles_i_assoc, liftCycles_i]

variable {S}

@[reassoc (attr := simp)]
lemma LeftHomologyData.leftHomologyπ_comp_leftHomologyIso_hom :
    S.leftHomologyπ ≫ h.leftHomologyIso.hom = h.cyclesIso.hom ≫ h.π := by
  dsimp only [leftHomologyπ, leftHomologyIso, cyclesIso, leftHomologyMapIso',
    cyclesMapIso', Iso.refl]
  rw [← leftHomologyπ_naturality']

@[reassoc (attr := simp)]
lemma LeftHomologyData.π_comp_leftHomologyIso_inv :
    h.π ≫ h.leftHomologyIso.inv = h.cyclesIso.inv ≫ S.leftHomologyπ := by
  simp only [← cancel_epi h.cyclesIso.hom, ← cancel_mono h.leftHomologyIso.hom, assoc,
    Iso.inv_hom_id, comp_id, Iso.hom_inv_id_assoc,
    LeftHomologyData.leftHomologyπ_comp_leftHomologyIso_hom]

@[reassoc (attr := simp)]
lemma LeftHomologyData.liftCycles_comp_cyclesIso_hom :
  S.liftCycles k hk ≫ h.cyclesIso.hom = h.liftK k hk :=
by simp only [← cancel_mono h.i, assoc, LeftHomologyData.cyclesIso_hom_comp_i,
  liftCycles_i, LeftHomologyData.liftK_i]

@[simp]
lemma LeftHomologyData.lift_K_comp_cyclesIso_inv :
    h.liftK k hk ≫ h.cyclesIso.inv = S.liftCycles k hk := by
  rw [← h.liftCycles_comp_cyclesIso_hom, assoc, Iso.hom_inv_id, comp_id]

lemma LeftHomologyData.ext_iff' (f₁ f₂ : S.leftHomology ⟶ A) :
    f₁ = f₂ ↔ h.π ≫ h.leftHomologyIso.inv ≫ f₁ = h.π ≫ h.leftHomologyIso.inv ≫ f₂ := by
  rw [← cancel_epi h.leftHomologyIso.inv, cancel_epi h.π]

end

namespace HasLeftHomology

variable (S)

lemma hasKernel [S.HasLeftHomology] : HasKernel S.g :=
⟨⟨⟨_, S.leftHomologyData.hi⟩⟩⟩

lemma hasCokernel [S.HasLeftHomology] [HasKernel S.g] :
    HasCokernel (kernel.lift S.g S.f S.zero) := by
  let h := S.leftHomologyData
  haveI : HasColimit (parallelPair h.f' 0) := ⟨⟨⟨_, h.hπ'⟩⟩⟩
  let e : parallelPair (kernel.lift S.g S.f S.zero) 0 ≅ parallelPair h.f' 0 :=
    parallelPair.ext (Iso.refl _)
      (IsLimit.conePointUniqueUpToIso (kernelIsKernel S.g) h.hi)
      (by aesop_cat) (by aesop_cat)
  exact hasColimitOfIso e

end HasLeftHomology

noncomputable def leftHomologyIsoCokernelLift [S.HasLeftHomology] [HasKernel S.g]
    [HasCokernel (kernel.lift S.g S.f S.zero)] :
    S.leftHomology ≅ cokernel (kernel.lift S.g S.f S.zero) :=
  (LeftHomologyData.ofKerOfCoker S).leftHomologyIso

namespace LeftHomologyData

lemma isIso_i_of_zero_g (h : LeftHomologyData S) (hg : S.g = 0) : IsIso h.i :=
  ⟨⟨h.liftK (𝟙 S.X₂) (by rw [hg, id_comp]),
    by simp only [← cancel_mono h.i, id_comp, assoc, liftK_i, comp_id], liftK_i _ _ _⟩⟩

end LeftHomologyData

end ShortComplex

end CategoryTheory
