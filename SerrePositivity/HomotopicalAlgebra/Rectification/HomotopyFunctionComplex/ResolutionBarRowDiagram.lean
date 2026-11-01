module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ResolutionCenterRowLaws
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ResolutionBarSimplexCone

/-!
# 中断した任意モデル源への一般化：ResolutionBarRowDiagram

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：One strict diagram of the underlying row cone maps over all nerve simplices。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0294][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0294
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# One strict diagram of the underlying row cone maps over all nerve simplices

Both row degrees and the first comma vertex move by actual functors.
The resulting natural transformations retain the original whole systems.
Their values are ordinary resolutions; no outer-frame functoriality is assumed.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra Opposite
open SerrePositivity.SimplicialModel SerrePositivity.NerveSimplexEndpoint

namespace SerrePositivity.HomotopyFunctionComplex.ResolutionBarRowDiagram
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (R : RightResolutionMapping.Index C)
local instance : ModelCategory (SimplexCategory ⥤ C) := Reedy.simplexModelCategory C
local instance : ModelCategory (SimplexCategory ⥤ Cᵒᵖ) := Reedy.simplexModelCategory Cᵒᵖ

abbrev Index := NerveSimplexEndpoint.Index (ResolutionBarCenters.Comma R)

def degrees : Index R ⥤ SimplexCategory where
  obj s := SimplexCategory.mk (dimension s)
  map f := operator f
  map_id _ := rfl
  map_comp _ _ := rfl

abbrev leftSource : Index R ⥤ ResolutionObject C :=
  degrees R ⋙ ResolutionFrameRows.functor R.1.unop.inner
abbrev rightSource : Index R ⥤ ResolutionObject Cᵒᵖ :=
  degrees R ⋙ ResolutionFrameRows.functor R.2.unop.inner

def leftTarget : Index R ⥤ ResolutionObject C where
  obj s := (NerveSimplexStart.start s).left.1.unop.inner
  map f := (NerveSimplexStart.startMap f).left.1.unop.map
  map_id s := by rw [NerveSimplexStart.startMap_id]; rfl
  map_comp f g := by rw [NerveSimplexStart.startMap_comp]; rfl

def rightTarget : Index R ⥤ ResolutionObject Cᵒᵖ where
  obj s := (NerveSimplexStart.start s).left.2.unop.inner
  map f := (NerveSimplexStart.startMap f).left.2.unop.map
  map_id s := by rw [NerveSimplexStart.startMap_id]; rfl
  map_comp f g := by rw [NerveSimplexStart.startMap_comp]; rfl

variable (a : NerveFirstChoice.System (ResolutionBarCenters.leftChoices R))
  (b : NerveFirstChoice.System (ResolutionBarCenters.rightChoices R))

def left : leftSource R ⟶ leftTarget R where
  app s := ResolutionCenterRowLifts.map C
    (ResolutionBarCenters.center R (NerveSimplexStart.start s)).1 (a.app s)
    (op (SimplexCategory.mk (dimension s))) (SSet.yonedaEquiv (𝟙 _))
  naturality {s t} f := by
    let q := (ResolutionBarCenters.center R (NerveSimplexStart.start t)).1
    let q' := (ResolutionBarCenters.center R (NerveSimplexStart.start s)).1
    let k : q' ⟶ q := ((ResolutionBarCenters.centers R).map
      (NerveSimplexStart.startMap f).op).1
    let z : SSet.stdSimplex.{v}.obj (SimplexCategory.mk (dimension t)) ⟶
        (ResolutionArrowDiagram.fibers C).obj q := a.app t
    let z' : SSet.stdSimplex.{v}.obj (SimplexCategory.mk (dimension s)) ⟶
        (ResolutionArrowDiagram.fibers C).obj q' := a.app s
    have ha := a.naturality f
    change SSet.stdSimplex.map (operator f) ≫ z = z' ≫
      (ResolutionArrowDiagram.fibers C).map k at ha
    have h := ResolutionCenterRowLaws.simplex C q z (operator f)
    rw [ha] at h
    have ht := h.trans (ResolutionCenterRowLifts.transport C k z'
      (op (SimplexCategory.mk (dimension s))) (SSet.yonedaEquiv (𝟙 _)))
    change ResolutionFrameRows.rowMap R.1.unop.inner (operator f) ≫
        ResolutionCenterRowLifts.map C q z (op (SimplexCategory.mk (dimension t)))
          (SSet.yonedaEquiv (𝟙 _)) =
      (ResolutionFrameRowFunctor.component (𝟙 R.1.unop) (SimplexCategory.mk (dimension s)) ≫
        ResolutionCenterRowLifts.map C q' z' (op (SimplexCategory.mk (dimension s)))
          (SSet.yonedaEquiv (𝟙 _))) ≫ (NerveSimplexStart.startMap f).left.1.unop.map at ht
    rw [ResolutionCenterRowLaws.component_id, Category.id_comp] at ht
    exact ht

def right : rightSource R ⟶ rightTarget R where
  app s := ResolutionCenterRowLifts.map Cᵒᵖ
    (ResolutionBarCenters.center R (NerveSimplexStart.start s)).2 (b.app s)
    (op (SimplexCategory.mk (dimension s))) (SSet.yonedaEquiv (𝟙 _))
  naturality {s t} f := by
    let q := (ResolutionBarCenters.center R (NerveSimplexStart.start t)).2
    let q' := (ResolutionBarCenters.center R (NerveSimplexStart.start s)).2
    let k : q' ⟶ q := ((ResolutionBarCenters.centers R).map
      (NerveSimplexStart.startMap f).op).2
    let z : SSet.stdSimplex.{v}.obj (SimplexCategory.mk (dimension t)) ⟶
        (ResolutionArrowDiagram.fibers Cᵒᵖ).obj q := b.app t
    let z' : SSet.stdSimplex.{v}.obj (SimplexCategory.mk (dimension s)) ⟶
        (ResolutionArrowDiagram.fibers Cᵒᵖ).obj q' := b.app s
    have hb := b.naturality f
    change SSet.stdSimplex.map (operator f) ≫ z = z' ≫
      (ResolutionArrowDiagram.fibers Cᵒᵖ).map k at hb
    have h := ResolutionCenterRowLaws.simplex Cᵒᵖ q z (operator f)
    rw [hb] at h
    have ht := h.trans (ResolutionCenterRowLifts.transport Cᵒᵖ k z'
      (op (SimplexCategory.mk (dimension s))) (SSet.yonedaEquiv (𝟙 _)))
    change ResolutionFrameRows.rowMap R.2.unop.inner (operator f) ≫
        ResolutionCenterRowLifts.map Cᵒᵖ q z (op (SimplexCategory.mk (dimension t)))
          (SSet.yonedaEquiv (𝟙 _)) =
      (ResolutionFrameRowFunctor.component (𝟙 R.2.unop) (SimplexCategory.mk (dimension s)) ≫
        ResolutionCenterRowLifts.map Cᵒᵖ q' z' (op (SimplexCategory.mk (dimension s)))
          (SSet.yonedaEquiv (𝟙 _))) ≫ (NerveSimplexStart.startMap f).left.2.unop.map at ht
    rw [ResolutionCenterRowLaws.component_id, Category.id_comp] at ht
    exact ht

lemma left_bar_recovery (n : SimplexCategoryᵒᵖ) (c : (ResolutionBarEvaluation.bar R).obj n) :
    (left R a).app (ofChain (ResolutionBarEvaluation.chain R n c)) =
      ResolutionBarSimplexCone.left R a n c := rfl

lemma right_bar_recovery (n : SimplexCategoryᵒᵖ) (c : (ResolutionBarEvaluation.bar R).obj n) :
    (right R b).app (ofChain (ResolutionBarEvaluation.chain R n c)) =
      ResolutionBarSimplexCone.right R b n c := rfl

end SerrePositivity.HomotopyFunctionComplex.ResolutionBarRowDiagram
