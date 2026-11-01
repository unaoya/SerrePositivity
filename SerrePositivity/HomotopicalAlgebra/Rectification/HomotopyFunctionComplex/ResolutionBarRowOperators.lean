module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ResolutionBarRowDiagram

/-!
# 中断した任意モデル源への一般化：ResolutionBarRowOperators

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：All chain operator squares of the same strict row cone diagram。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0296][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0296
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# All chain operator squares of the same strict row cone diagram

These are the naturality squares of the actual global natural transformations,
with the actual prefix maps. No outer-frame functoriality is inferred.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra Opposite
open SerrePositivity.SimplicialModel SerrePositivity.NerveSimplexEndpoint

namespace SerrePositivity.HomotopyFunctionComplex.ResolutionBarRowOperators
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (R : RightResolutionMapping.Index C)
  (a : NerveFirstChoice.System (ResolutionBarCenters.leftChoices R))
  (b : NerveFirstChoice.System (ResolutionBarCenters.rightChoices R))

abbrev left {n : ℕ} (c : ComposableArrows (ResolutionBarCenters.Comma R) n) :=
  (ResolutionBarRowDiagram.left R a).app (ofChain c)
abbrev right {n : ℕ} (c : ComposableArrows (ResolutionBarCenters.Comma R) n) :=
  (ResolutionBarRowDiagram.right R b).app (ofChain c)

lemma left_operator {n m : ℕ} (c : ComposableArrows (ResolutionBarCenters.Comma R) n)
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    ResolutionFrameRows.rowMap R.1.unop.inner θ ≫ left R a c =
      left R a ((SimplexCategory.toCat.map θ).toFunctor ⋙ c) ≫
        (c.map (homOfLE (Fin.zero_le (θ.toOrderHom 0)))).left.1.unop.map := by
  have h := (ResolutionBarRowDiagram.left R a).naturality (reindexArrow c θ)
  change ResolutionFrameRows.rowMap R.1.unop.inner θ ≫ left R a c =
    left R a ((SimplexCategory.toCat.map θ).toFunctor ⋙ c) ≫
      (NerveSimplexStart.startMap (reindexArrow c θ)).left.1.unop.map at h
  rw [NerveSimplexStart.reindexArrow_start] at h
  exact h

lemma right_operator {n m : ℕ} (c : ComposableArrows (ResolutionBarCenters.Comma R) n)
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    ResolutionFrameRows.rowMap R.2.unop.inner θ ≫ right R b c =
      right R b ((SimplexCategory.toCat.map θ).toFunctor ⋙ c) ≫
        (c.map (homOfLE (Fin.zero_le (θ.toOrderHom 0)))).left.2.unop.map := by
  have h := (ResolutionBarRowDiagram.right R b).naturality (reindexArrow c θ)
  change ResolutionFrameRows.rowMap R.2.unop.inner θ ≫ right R b c =
    right R b ((SimplexCategory.toCat.map θ).toFunctor ⋙ c) ≫
      (NerveSimplexStart.startMap (reindexArrow c θ)).left.2.unop.map at h
  rw [NerveSimplexStart.reindexArrow_start] at h
  exact h

lemma left_recovery (n : SimplexCategoryᵒᵖ) (c : (ResolutionBarEvaluation.bar R).obj n) :
    left R a (ResolutionBarEvaluation.chain R n c) = ResolutionBarSimplexCone.left R a n c :=
  ResolutionBarRowDiagram.left_bar_recovery R a n c

lemma right_recovery (n : SimplexCategoryᵒᵖ) (c : (ResolutionBarEvaluation.bar R).obj n) :
    right R b (ResolutionBarEvaluation.chain R n c) = ResolutionBarSimplexCone.right R b n c :=
  ResolutionBarRowDiagram.right_bar_recovery R b n c

end SerrePositivity.HomotopyFunctionComplex.ResolutionBarRowOperators
