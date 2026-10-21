module

public import SerrePositivity.InfinityCategories.F1.CocartesianScaffoldLocalPathLifting
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

variable (n : ℕ) {C : Type u} [Category.{u} C] (k : ULift.{u} (Fin (n + 2)) ⥤ C)
  (p q : CocartesianFibrationCategory (nerve C))

/-- 同じ共有頂点成分を保った最初の脚の、元の自然性 path を持ち上げる厳密化。 -/
def cocartesianScaffoldCorrectedFirstSquare :
    PathCorrectedFunctorSquare
      ((cocartesianScaffoldLocalTarget n k p q).map WalkingCospan.Hom.inl)
      (cocartesianScaffoldLocalComparison n k p q WalkingCospan.left)
      ((cocartesianScaffoldLocalSource n k p q).map WalkingCospan.Hom.inl ≫
        cocartesianScaffoldLocalComparison n k p q WalkingCospan.one)
      (cocartesianScaffoldLocalComparison_firstIso n k p q) :=
  pathCorrectedFunctorSquare _
    (cocartesianScaffoldLocalTarget_first_kanEquivalenceLifting n k p q) _ _ _

/-- 同じ共有頂点成分を保った次の脚の、元の自然性 path を持ち上げる厳密化。 -/
def cocartesianScaffoldCorrectedSecondSquare :
    PathCorrectedFunctorSquare
      ((cocartesianScaffoldLocalTarget n k p q).map WalkingCospan.Hom.inr)
      (cocartesianScaffoldLocalComparison n k p q WalkingCospan.right)
      ((cocartesianScaffoldLocalSource n k p q).map WalkingCospan.Hom.inr ≫
        cocartesianScaffoldLocalComparison n k p q WalkingCospan.one)
      (cocartesianScaffoldLocalComparison_secondIso n k p q) :=
  pathCorrectedFunctorSquare _
    (cocartesianScaffoldLocalTarget_second_kanEquivalenceLifting n k p q) _ _ _

end SerrePositivity.InfinityCategories
