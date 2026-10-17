module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ResolutionCenterRowLifts

/-!
# 中断した任意モデル源への一般化：ResolutionCenterRowLaws

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Whole-map restriction laws for actual center row lifts。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0301][inventory]を参照する。

[inventory]: ../../../../formalization-plans/k-theory-generalization-inventory.md#m0301
[plan]: ../../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Whole-map restriction laws for actual center row lifts
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra Opposite

namespace SerrePositivity.HomotopyFunctionComplex.ResolutionCenterRowLaws
variable (C : Type u) [Category.{v} C] [ModelCategory C]
local instance : ModelCategory (SimplexCategory ⥤ C) := Reedy.simplexModelCategory C

lemma parameter (q : ResolutionArrowDiagram.Index C) {T U : SSet.{v}} (i : U ⟶ T)
    (s : T ⟶ (ResolutionArrowDiagram.fibers C).obj q) (n : SimplexCategoryᵒᵖ) (x : U.obj n) :
    ResolutionCenterRowLifts.map C q (i ≫ s) n x =
      ResolutionCenterRowLifts.map C q s n (i.app n x) := rfl

lemma simplex (q : ResolutionArrowDiagram.Index C) {n m : SimplexCategory}
    (s : SSet.stdSimplex.{v}.obj n ⟶ (ResolutionArrowDiagram.fibers C).obj q) (θ : m ⟶ n) :
    ResolutionFrameRows.rowMap (ResolutionArrowDiagram.source C q).inner θ ≫
        ResolutionCenterRowLifts.map C q s (op n) (SSet.yonedaEquiv (𝟙 _)) =
      ResolutionCenterRowLifts.map C q (SSet.stdSimplex.map θ ≫ s)
        (op m) (SSet.yonedaEquiv (𝟙 _)) := by
  rw [parameter]
  have h := ResolutionCenterRowLifts.naturality C q s θ.op (SSet.yonedaEquiv (𝟙 _))
  have he : (SSet.stdSimplex.{v}.obj n).map θ.op (SSet.yonedaEquiv (𝟙 _)) =
      (SSet.stdSimplex.map θ).app (op m) (SSet.yonedaEquiv (𝟙 _)) := by
    apply ULift.ext
    change θ ≫ 𝟙 n = 𝟙 m ≫ θ
    simp only [Category.id_comp, Category.comp_id]
  rw [he] at h
  exact h

lemma component_id (X : FramedResolution C) (n : SimplexCategory) :
    ResolutionFrameRowFunctor.component (𝟙 X) n = 𝟙 (ResolutionFrameRows.row X.inner n) := by
  apply ResolutionObject.Hom.ext <;> rfl

end SerrePositivity.HomotopyFunctionComplex.ResolutionCenterRowLaws
