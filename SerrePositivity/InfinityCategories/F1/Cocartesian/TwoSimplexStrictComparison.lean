module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.TwoSimplexCorrectedSquares

/-!
概要：同じ局所 cospan の比較を、全成分が同値な厳密な自然変換へ束ねる。
方針：元の共有頂点成分と、元の自然性 path を保持する二つの補正成分を使う。
規約：元の成分との同型および標的 path の一致は補正正方形に保持する。
使われ方：二次元 Segal 比較の実際の pullback 上の同値。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories

variable {C : Type u} [Category.{u} C] (k : ULift.{u} (Fin 3) ⥤ C)
  (p q : CocartesianFibrationCategory (nerve C))

/-- 元の共有頂点比較を保ち、同じ二脚で厳密に可換な局所 cospan の自然変換。 -/
def cocartesianTwoSimplexStrictComparison :
    cocartesianTwoSimplexLocalSource k p q ⟶ cocartesianTwoSimplexLocalTarget k p q :=
  cospanHomMk
    (cocartesianTwoSimplexLocalComparison k p q WalkingCospan.one)
    (cocartesianTwoSimplexCorrectedFirstSquare k p q).map
    (cocartesianTwoSimplexCorrectedSecondSquare k p q).map
    (cocartesianTwoSimplexCorrectedFirstSquare k p q).comm.symm
    (cocartesianTwoSimplexCorrectedSecondSquare k p q).comm.symm

/-- 同じ厳密な cospan 比較は、三成分とも元の局所比較と同型な同値。 -/
lemma cocartesianTwoSimplexStrictComparison_isQCatEquivalence (j : WalkingCospan) :
    IsQCatEquivalence ((cocartesianTwoSimplexStrictComparison k p q).app j) := by
  cases j with
  | none => exact cocartesianTwoSimplexLocalComparison_isQCatEquivalence k p q WalkingCospan.one
  | some j =>
    cases j with
    | left =>
      exact (cocartesianTwoSimplexCorrectedFirstSquare k p q).map_isQCatEquivalence
        (cocartesianTwoSimplexLocalComparison_isQCatEquivalence k p q WalkingCospan.left)
    | right =>
      exact (cocartesianTwoSimplexCorrectedSecondSquare k p q).map_isQCatEquivalence
        (cocartesianTwoSimplexLocalComparison_isQCatEquivalence k p q WalkingCospan.right)

end SerrePositivity.InfinityCategories
