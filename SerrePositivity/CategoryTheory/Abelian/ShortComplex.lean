module

public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.CategoryTheory.Retract
public import Mathlib.CategoryTheory.Abelian.Basic

/-! # 完全な短複体の小さな補題

## 概要

完全な対の像と余像の短完全列、直和因子が短複体の完全性を保つこと（`Exact.of_retract`）、選んだ余核と短完全列の最後の項の比較を与える。

## 方針

余核の比較は `(cokernelIsCokernel _).coconePointUniqueUpToIso hS.gIsCokernel` の形で書く。

## 規約

`Exact.of_retract` は Mathlib にない（提出候補）。

## 使われ方

KTheory の Adams 作用の核・余核。
-/

@[expose] public noncomputable section

universe v u

section ExactImageSequencePart

namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits
variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The image of the first map and coimage of the second map meet at the middle object. -/
abbrev imageCoimageShortComplex (S : ShortComplex A) : ShortComplex A :=
  ShortComplex.mk (Abelian.image.ι S.f) (Abelian.coimage.π S.g)
    (Abelian.comp_coimage_π_eq_zero (Abelian.image_ι_comp_eq_zero S.zero))

/-- Exactness of the original pair makes the image–coimage sequence short exact. -/
lemma imageCoimageShortComplex_shortExact {S : ShortComplex A} (hS : S.Exact) :
    (imageCoimageShortComplex S).ShortExact := by
  let S' := ShortComplex.mk (Abelian.image.ι S.f) S.g (Abelian.image_ι_comp_eq_zero S.zero)
  have hS' : S'.Exact := S.exact_iff_exact_image_ι.mp hS
  exact { exact := S'.exact_iff_exact_coimage_π.mp hS' }

end SerrePositivity

end ExactImageSequencePart

section ExactRetractPart

namespace SerrePositivity

open CategoryTheory CategoryTheory.Limits

variable {A : Type*} [Category* A] [Abelian A]

/-- 完全な短複体の retract は完全である。 -/
lemma shortComplex_exact_of_retract {S T : ShortComplex A} (r : Retract S T)
    (hT : T.Exact) : S.Exact := by
  rw [ShortComplex.exact_iff_isZero_homology] at hT ⊢
  let h := r.map (ShortComplex.homologyFunctor A)
  change IsZero ((ShortComplex.homologyFunctor A).obj S)
  rw [IsZero.iff_id_eq_zero, ← h.retract]
  have hz : h.r = 0 := hT.eq_zero_of_src h.r
  rw [hz, comp_zero]

end SerrePositivity

end ExactRetractPart

section ShortExactCokernelPart

namespace SerrePositivity
open CategoryTheory Category Limits

/-- Compare the chosen cokernel of a short exact sequence with its final object. -/
def shortExactCokernelIso
    {C : Type*} [Category C] [Abelian C] (T : ShortComplex C) (hT : T.ShortExact) :
    cokernel T.f ≅ T.X₃ :=
  (cokernelIsCokernel T.f).coconePointUniqueUpToIso hT.gIsCokernel

@[reassoc]
lemma shortExactCokernelIso_π_hom
    {C : Type*} [Category C] [Abelian C] (T : ShortComplex C) (hT : T.ShortExact) :
    cokernel.π T.f ≫ (shortExactCokernelIso T hT).hom = T.g :=
  (cokernelIsCokernel T.f).comp_coconePointUniqueUpToIso_hom
    hT.gIsCokernel WalkingParallelPair.one

namespace Adams

/-- Compatibility name for the common short exact cokernel comparison. -/
abbrev shortExactCokernelIso
    {C : Type*} [Category C] [Abelian C] (T : ShortComplex C) (hT : T.ShortExact) :
    cokernel T.f ≅ T.X₃ := SerrePositivity.shortExactCokernelIso T hT

end Adams
end SerrePositivity

end ShortExactCokernelPart
