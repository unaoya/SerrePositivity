module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ResolutionCenterRowLifts
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ResolutionBarRowPresentations

/-!
# 中断した任意モデル源への一般化：ResolutionBarSimplexCone

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Each actual bar simplex maps to its exact evaluated row presentation。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0298][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0298
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Each actual bar simplex maps to its exact evaluated row presentation

The source vertex and its original Hom label are retained. Both lift
families give full resolution maps and hence an actual element comma arrow.
This does not assert a simplicial contraction of the entire bar.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra Opposite
open SerrePositivity.SimplicialModel SerrePositivity.NerveSimplexEndpoint

namespace SerrePositivity.HomotopyFunctionComplex.ResolutionBarSimplexCone
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (R : RightResolutionMapping.Index C)
  (a : NerveFirstChoice.System (ResolutionBarCenters.leftChoices R))
  (b : NerveFirstChoice.System (ResolutionBarCenters.rightChoices R))
local instance : ModelCategory (SimplexCategory ⥤ C) := Reedy.simplexModelCategory C
local instance : ModelCategory (SimplexCategory ⥤ Cᵒᵖ) := Reedy.simplexModelCategory Cᵒᵖ

def left (n : SimplexCategoryᵒᵖ) (c : (ResolutionBarEvaluation.bar R).obj n) :
    ResolutionFrameRows.row R.1.unop.inner n.unop ⟶ (c.obj 0).left.obj.1.unop.inner :=
  ResolutionCenterRowLifts.map C
    (ResolutionBarCenters.center R ((ResolutionBarEvaluation.chain R n c).obj 0)).1
    (a.app (ofChain (ResolutionBarEvaluation.chain R n c))) n (SSet.yonedaEquiv (𝟙 _))

def right (n : SimplexCategoryᵒᵖ) (c : (ResolutionBarEvaluation.bar R).obj n) :
    ResolutionFrameRows.row R.2.unop.inner n.unop ⟶ (c.obj 0).left.obj.2.unop.inner :=
  ResolutionCenterRowLifts.map Cᵒᵖ
    (ResolutionBarCenters.center R ((ResolutionBarEvaluation.chain R n c).obj 0)).2
    (b.app (ofChain (ResolutionBarEvaluation.chain R n c))) n (SSet.yonedaEquiv (𝟙 _))

def arrow (n : SimplexCategoryᵒᵖ) (c : (ResolutionBarEvaluation.bar R).obj n) :
    (c.obj 0).left.obj ⟶ ResolutionBarRowPresentations.pair R n :=
  ((FramedResolution.lift (left R a n c)).op, (FramedResolution.lift (right R b n c)).op)

lemma arrow_base (n : SimplexCategoryᵒᵖ) (c : (ResolutionBarEvaluation.bar R).obj n) :
    (RightResolutionMapping.projection (C := C)).map (arrow R a b n c) = (c.obj 0).hom := rfl

lemma arrow_label (n : SimplexCategoryᵒᵖ) (c : (ResolutionBarEvaluation.bar R).obj n) :
    ((MixedBiresolutionComparison.functor (C := C)).map (arrow R a b n c)).app n
        (c.obj 0).left.val = ((ResolutionBarEvaluation.evaluation R a b).app n c).down := by
  change (left R a n c).diagram.app n.unop ≫ (c.obj 0).left.val ≫
    ((right R b n c).diagram.app n.unop).unop = _
  dsimp only [left, right]
  rw [ResolutionCenterRowLifts.diagram, ResolutionCenterRowLifts.diagram]
  let t : SSet.stdSimplex.{v}.obj n.unop ⟶
      (MixedBiresolutionComparison.functor (C := C)).obj (c.obj 0).left.obj :=
    SSet.yonedaEquiv.symm (c.obj 0).left.val
  change _ = _ ≫ t.app n (SSet.yonedaEquiv (𝟙 _)) ≫ _
  have ht : t.app n (SSet.yonedaEquiv (𝟙 _)) = (c.obj 0).left.val :=
    SSet.yonedaEquiv_symm_app_id _
  rw [ht]
  rfl

abbrev element (n : SimplexCategoryᵒᵖ) (c : (ResolutionBarEvaluation.bar R).obj n) :
    CostructuredArrow (BarConstruction.elementProjection
      (RightResolutionMapping.projection (C := C)) MixedBiresolutionComparison.functor n)
      ((RightResolutionMapping.projection (C := C)).obj R) :=
  CostructuredArrow.mk
    (Y := ((MixedBiresolutionComparison.functor (C := C)).flip.obj n).elementsMk
      (ResolutionBarRowPresentations.pair R n)
      (((ResolutionBarEvaluation.evaluation R a b).app n c).down)) (𝟙 _)

/-- A genuine arrow in the same element comma category defining the source bar degree. -/
def elementArrow (n : SimplexCategoryᵒᵖ) (c : (ResolutionBarEvaluation.bar R).obj n) :
    c.obj 0 ⟶ element R a b n c :=
  CostructuredArrow.homMk (Functor.Elements.homMk (arrow R a b n c) (arrow_label R a b n c))
    (by
      change (RightResolutionMapping.projection (C := C)).map (arrow R a b n c) ≫ 𝟙 _ = _
      rw [arrow_base, Category.comp_id])

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

include hcof hfib in
lemma arrow_raw_weakEquivalence (n : SimplexCategoryᵒᵖ)
    (c : (ResolutionBarEvaluation.bar R).obj n)
    (hs : weakEquivalences C (c.obj 0).hom.1.unop)
    (ht : weakEquivalences Cᵒᵖ (c.obj 0).hom.2.op) :
    weakEquivalences SSet.{v}
      ((MixedBiresolutionComparison.functor (C := C)).map (arrow R a b n c)) :=
  MixedResolutionInvariance.map_weakEquivalence hcof hfib (arrow R a b n c) hs ht

end SerrePositivity.HomotopyFunctionComplex.ResolutionBarSimplexCone
