module

public import SerrePositivity.InfinityCategories.F1.CocartesianTwoSimplexLocalPathLifting
public import SerrePositivity.InfinityCategories.F1.PathCorrectedFunctorSquare

/-!
概要：元の局所 cospan の二つの自然性を、指定 path を保って厳密可換にする。
方針：元の共有頂点成分を固定し、標的の両脚の相対 path 持ち上げを使う。
規約：元の辺成分への path と、元の自然性を表す標的 path を保存する。
使われ方：同じ三成分の同値による厳密な pullback 比較。
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

/-- 同じ共有頂点成分を保った最初の脚の、元の自然性 path を持ち上げる厳密化。 -/
def cocartesianTwoSimplexCorrectedFirstSquare :
    PathCorrectedFunctorSquare
      ((cocartesianTwoSimplexLocalTarget k p q).map WalkingCospan.Hom.inl)
      (cocartesianTwoSimplexLocalComparison k p q WalkingCospan.left)
      ((cocartesianTwoSimplexLocalSource k p q).map WalkingCospan.Hom.inl ≫
        cocartesianTwoSimplexLocalComparison k p q WalkingCospan.one)
      (cocartesianTwoSimplexLocalComparison_firstIso k p q) :=
  pathCorrectedFunctorSquare _
    (cocartesianTwoSimplexLocalTarget_first_kanEquivalenceLifting k p q) _ _ _

/-- 同じ共有頂点成分を保った次の脚の、元の自然性 path を持ち上げる厳密化。 -/
def cocartesianTwoSimplexCorrectedSecondSquare :
    PathCorrectedFunctorSquare
      ((cocartesianTwoSimplexLocalTarget k p q).map WalkingCospan.Hom.inr)
      (cocartesianTwoSimplexLocalComparison k p q WalkingCospan.right)
      ((cocartesianTwoSimplexLocalSource k p q).map WalkingCospan.Hom.inr ≫
        cocartesianTwoSimplexLocalComparison k p q WalkingCospan.one)
      (cocartesianTwoSimplexLocalComparison_secondIso k p q) :=
  pathCorrectedFunctorSquare _
    (cocartesianTwoSimplexLocalTarget_second_kanEquivalenceLifting k p q) _ _ _

end SerrePositivity.InfinityCategories
