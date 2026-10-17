module

public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NormalizedHornTargetComposition

/-!
# 中断した任意モデル源への一般化：NormalizedHornTargetFaces

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Whole faces of the selected target composition triangle。

## 方針（定義・証明）
全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0503][inventory]を参照する。

[inventory]: ../../../../formalization-plans/k-theory-generalization-inventory.md#m0503
[plan]: ../../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Whole faces of the selected target composition triangle
-/

@[expose] public section
universe v
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

namespace SerrePositivity.SimplicialModel.NormalizedHornTargetFaces
variable {K L M : SSet.{v}} {n : ℕ} (i : Fin (n + 2))
  (hK : SSet.modelCategoryQuillen.J.rlp (terminal.from K))
  (hL : SSet.modelCategoryQuillen.J.rlp (terminal.from L))
  (hM : SSet.modelCategoryQuillen.J.rlp (terminal.from M)) (q : K ⟶ L) (r : L ⟶ M)

lemma zero : _ ◁ SSet.stdSimplex.δ (0 : Fin 3) ≫
    NormalizedHornTargetComposition.triangle i hK hL hM q r =
    ((ihom (SSet.horn (n + 1) i).toSSet).map q) ▷
      SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫
        (NormalizedHornTargetComparison.comparison i hL hM r).h := by
  rw [NormalizedHornTargetComposition.triangle_face]
  exact NormalizedHornTargetComposition.second_h i hL hM q r

lemma one : _ ◁ SSet.stdSimplex.δ (1 : Fin 3) ≫
    NormalizedHornTargetComposition.triangle i hK hL hM q r =
      (NormalizedHornTargetComparison.comparison i hK hM (q ≫ r)).h :=
  NormalizedHornTargetComposition.triangle_face i hK hL hM q r 1

lemma two : _ ◁ SSet.stdSimplex.δ (2 : Fin 3) ≫
    NormalizedHornTargetComposition.triangle i hK hL hM q r =
    (NormalizedHornTargetComparison.comparison i hK hL q).h ≫
      (ihom (SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)))).map r := by
  rw [NormalizedHornTargetComposition.triangle_face]
  exact NormalizedHornTargetComposition.first_h i hK hL q r

end SerrePositivity.SimplicialModel.NormalizedHornTargetFaces
