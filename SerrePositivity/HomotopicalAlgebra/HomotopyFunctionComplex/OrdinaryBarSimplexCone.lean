module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionCenterRowLifts
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarEvaluation
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryResolutionRows

/-!
# 中断した任意モデル源への一般化：OrdinaryBarSimplexCone

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
再開時は[計画書 §396][plan]と[棚卸し m0218][inventory]を参照する。

[inventory]: ../../../formalization-plans/k-theory-generalization-inventory.md#m0218
[plan]: ../../../formalization-plans/k-theory.md
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

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarSimplexCone
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (R : RightResolutionMapping.Index C)
  (a : NerveFirstChoice.System (OrdinaryBarCenters.leftChoices R))
  (b : NerveFirstChoice.System (OrdinaryBarCenters.rightChoices R))
local instance : ModelCategory (SimplexCategory ⥤ C) := Reedy.simplexModelCategory C
local instance : ModelCategory (SimplexCategory ⥤ Cᵒᵖ) := Reedy.simplexModelCategory Cᵒᵖ

def left (n : SimplexCategoryᵒᵖ) (c : (OrdinaryBarEvaluation.bar R).obj n) :
    ResolutionFrameRows.row R.1.unop.inner n.unop ⟶ (c.obj 0).left.obj.1.unop :=
  ResolutionCenterRowLifts.map C
    (OrdinaryBarCenters.center R ((OrdinaryBarEvaluation.chain R n c).obj 0)).1
    (a.app (ofChain (OrdinaryBarEvaluation.chain R n c))) n (SSet.yonedaEquiv (𝟙 _))

def right (n : SimplexCategoryᵒᵖ) (c : (OrdinaryBarEvaluation.bar R).obj n) :
    ResolutionFrameRows.row R.2.unop.inner n.unop ⟶ (c.obj 0).left.obj.2.unop :=
  ResolutionCenterRowLifts.map Cᵒᵖ
    (OrdinaryBarCenters.center R ((OrdinaryBarEvaluation.chain R n c).obj 0)).2
    (b.app (ofChain (OrdinaryBarEvaluation.chain R n c))) n (SSet.yonedaEquiv (𝟙 _))

def arrow (n : SimplexCategoryᵒᵖ) (c : (OrdinaryBarEvaluation.bar R).obj n) :
    (c.obj 0).left.obj ⟶ (OrdinaryResolutionRows.rows R).obj n :=
  ((left R a n c).op, (right R b n c).op)

lemma arrow_base (n : SimplexCategoryᵒᵖ) (c : (OrdinaryBarEvaluation.bar R).obj n) :
    (OrdinaryResolutionPairs.projection (C := C)).map (arrow R a b n c) = (c.obj 0).hom := rfl

lemma arrow_label (n : SimplexCategoryᵒᵖ) (c : (OrdinaryBarEvaluation.bar R).obj n) :
    ((OrdinaryResolutionPairs.raw (C := C)).map (arrow R a b n c)).app n
        (c.obj 0).left.val = ((OrdinaryBarEvaluation.evaluation R a b).app n c).down := by
  change (left R a n c).diagram.app n.unop ≫ (c.obj 0).left.val ≫
    ((right R b n c).diagram.app n.unop).unop = _
  dsimp only [left, right]
  rw [ResolutionCenterRowLifts.diagram, ResolutionCenterRowLifts.diagram]
  let t : SSet.stdSimplex.{v}.obj n.unop ⟶
      (OrdinaryResolutionPairs.raw (C := C)).obj (c.obj 0).left.obj :=
    SSet.yonedaEquiv.symm (c.obj 0).left.val
  change _ = _ ≫ t.app n (SSet.yonedaEquiv (𝟙 _)) ≫ _
  have ht : t.app n (SSet.yonedaEquiv (𝟙 _)) = (c.obj 0).left.val :=
    SSet.yonedaEquiv_symm_app_id _
  rw [ht]
  rfl

abbrev element (n : SimplexCategoryᵒᵖ) (c : (OrdinaryBarEvaluation.bar R).obj n) :
    CostructuredArrow (BarConstruction.elementProjection
      (OrdinaryResolutionPairs.projection (C := C)) OrdinaryResolutionPairs.raw n)
      ((OrdinaryResolutionPairs.projection (C := C)).obj
        (OrdinaryResolutionPairs.forgetFrames.obj R)) :=
  CostructuredArrow.mk
    (Y := ((OrdinaryResolutionPairs.raw (C := C)).flip.obj n).elementsMk
      ((OrdinaryResolutionRows.rows R).obj n)
      (((OrdinaryBarEvaluation.evaluation R a b).app n c).down)) (𝟙 _)

/-- A genuine arrow in the same element comma category defining the source bar degree. -/
def elementArrow (n : SimplexCategoryᵒᵖ) (c : (OrdinaryBarEvaluation.bar R).obj n) :
    c.obj 0 ⟶ element R a b n c :=
  CostructuredArrow.homMk (Functor.Elements.homMk (arrow R a b n c) (arrow_label R a b n c))
    (by
      change (OrdinaryResolutionPairs.projection (C := C)).map (arrow R a b n c) ≫ 𝟙 _ = _
      rw [arrow_base, Category.comp_id])

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

include hcof hfib in
lemma arrow_raw_weakEquivalence (n : SimplexCategoryᵒᵖ)
    (c : (OrdinaryBarEvaluation.bar R).obj n)
    (hs : weakEquivalences C (c.obj 0).hom.1.unop)
    (ht : weakEquivalences Cᵒᵖ (c.obj 0).hom.2.op) :
    weakEquivalences SSet.{v}
      ((OrdinaryResolutionPairs.raw (C := C)).map (arrow R a b n c)) :=
  MixedResolutionInvariance.lift_map_weakEquivalence hcof hfib
    (left R a n c) (right R b n c) hs ht

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarSimplexCone
