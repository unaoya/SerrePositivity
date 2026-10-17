module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.CosimplicialDegenerateHorn
public import SerrePositivity.HomotopicalAlgebra.Simplicial.BoundaryCotensor

/-!
# 中断した任意モデル源への一般化：DegenerateHornOverlap

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Any two degenerate whole horn families agree on their overlap。

## 方針（定義・証明）
全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0378][inventory]を参照する。

[inventory]: ../../../formalization-plans/k-theory-generalization-inventory.md#m0378
[plan]: ../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Any two degenerate whole horn families agree on their overlap

Transposition puts the whole external parameter into the target. The
cosimplicial uniqueness argument then applies in every dimension and
for every pair of degeneracies, without any Kan assumption.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalClosed

namespace SerrePositivity.SimplicialModel.DegenerateHornOverlap
variable (K : SSet.{v}) {n : ℕ} (i : Fin (n + 2)) (j k : Fin (n + 1))
  {L : SSet.{v}} (a b : L ⟶ (ihom (SSet.stdSimplex.obj (SimplexCategory.mk n))).obj K)

lemma eq_of_same_horn
    (h : a ≫ DegenerateHornInput.boundary i j K = b ≫ DegenerateHornInput.boundary i k K) :
    a ≫ DegenerateHornInput.degeneracy j K = b ≫ DegenerateHornInput.degeneracy k K := by
  have ht := congrArg BoundaryCotensor.transpose h
  change BoundaryCotensor.transpose
      ((a ≫ (pre (SSet.stdSimplex.σ j)).app K) ≫ (pre (SSet.horn (n + 1) i).ι).app K) =
    BoundaryCotensor.transpose
      ((b ≫ (pre (SSet.stdSimplex.σ k)).app K) ≫ (pre (SSet.horn (n + 1) i).ι).app K) at ht
  simp only [BoundaryCotensor.transpose_restriction] at ht
  have hf : ∀ r : Fin (n + 2), r ≠ i →
      SSet.stdSimplex.δ r ≫ SSet.stdSimplex.σ j ≫ BoundaryCotensor.transpose a =
        SSet.stdSimplex.δ r ≫ SSet.stdSimplex.σ k ≫ BoundaryCotensor.transpose b := by
    intro r hr
    have he := congrArg (fun q => SSet.horn.ι i r hr ≫ q) ht
    simpa only [← Category.assoc, SSet.horn.ι_ι] using he
  apply BoundaryCotensor.transpose_injective
  change BoundaryCotensor.transpose (a ≫ (pre (SSet.stdSimplex.σ j)).app K) =
    BoundaryCotensor.transpose (b ≫ (pre (SSet.stdSimplex.σ k)).app K)
  rw [BoundaryCotensor.transpose_restriction, BoundaryCotensor.transpose_restriction]
  exact CosimplicialDegenerateHorn.eq_of_faces SSet.stdSimplex i j k
    (BoundaryCotensor.transpose a) (BoundaryCotensor.transpose b) hf

end SerrePositivity.SimplicialModel.DegenerateHornOverlap
