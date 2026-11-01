module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ResolutionBarRowOperators

/-!
# 中断した任意モデル源への一般化：ResolutionBarConeDiagram

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：One strict underlying cone diagram on the actual bar simplex category。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0289][inventory]を参照する。

[inventory]: ../../../../formalization-plans/k-theory-generalization-inventory.md#m0289
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# One strict underlying cone diagram on the actual bar simplex category

Forgetting labels is a genuine simplicial map. Pulling the row diagram
back along its element functor retains every original simplex cone map.
The values are ordinary resolutions, before any outer-frame lift choices.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra Opposite
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.ResolutionBarConeDiagram
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (R : RightResolutionMapping.Index C)

/-- Forget only the Hom labels, keeping the same actual comma chains. -/
def forgetLabels : ResolutionBarEvaluation.bar R ⟶ nerve (ResolutionBarCenters.Comma R) where
  app n := ↾fun c => ResolutionBarEvaluation.chain R n c
  naturality {n m} θ := by
    apply ConcreteCategory.hom_ext
    intro c
    exact ResolutionBarEvaluation.chain_operator R θ c

abbrev Index := (ResolutionBarEvaluation.bar R).Elementsᵒᵖ
abbrev indices : Index R ⥤ ResolutionBarRowDiagram.Index R := (forgetLabels R).mapElements.op
abbrev leftSource := indices R ⋙ ResolutionBarRowDiagram.leftSource R
abbrev rightSource := indices R ⋙ ResolutionBarRowDiagram.rightSource R
abbrev leftTarget := indices R ⋙ ResolutionBarRowDiagram.leftTarget R
abbrev rightTarget := indices R ⋙ ResolutionBarRowDiagram.rightTarget R

variable (a : NerveFirstChoice.System (ResolutionBarCenters.leftChoices R))
  (b : NerveFirstChoice.System (ResolutionBarCenters.rightChoices R))

abbrev left : leftSource R ⟶ leftTarget R :=
  Functor.whiskerLeft (indices R) (ResolutionBarRowDiagram.left R a)
abbrev right : rightSource R ⟶ rightTarget R :=
  Functor.whiskerLeft (indices R) (ResolutionBarRowDiagram.right R b)

lemma left_recovery (n : SimplexCategoryᵒᵖ) (c : (ResolutionBarEvaluation.bar R).obj n) :
    (left R a).app (op ((ResolutionBarEvaluation.bar R).elementsMk n c)) =
      ResolutionBarSimplexCone.left R a n c :=
  ResolutionBarRowDiagram.left_bar_recovery R a n c

lemma right_recovery (n : SimplexCategoryᵒᵖ) (c : (ResolutionBarEvaluation.bar R).obj n) :
    (right R b).app (op ((ResolutionBarEvaluation.bar R).elementsMk n c)) =
      ResolutionBarSimplexCone.right R b n c :=
  ResolutionBarRowDiagram.right_bar_recovery R b n c

end SerrePositivity.HomotopyFunctionComplex.ResolutionBarConeDiagram
