module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.RightFibrationEdgeComposition
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.FixedApexLimitCriterion

/-!
概要：指定された錐の辺に沿う、固定頂点の錐の比較の自然性。
方針：slice の right fibration に辺の全族比較を適用する。
規約：極限性は不要。使われ方：G8 の指定極限錐への比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories
open TheSliceAndJoinConstructions MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes

namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces

/-- 概要：固定頂点の錐への元の比較は、錐の指定辺の標準後合成と全族で可換。
方針：slice 射影の辺の比較を、元の錐の族への射で後合成する。
規約：錐とその辺を入力とし、同型は仮定しない。
使われ方：G8 の選んだ極限頂点の辺の比較。 -/
def fixedApexConeHomComparison_edgeIso {K X : SSet.{u}} [Quasicategory X]
    {p : K ⟶ X} {c d : JoinCone p} (e : (sliceOver p).Edge c d) (x : X _⦋0⦌) :
    FunctorIso (fixedApexConeHomComparison c x)
      (postcompose x (SSet.Truncated.HomotopyCategory.homMk
        (e.map (sliceOverProjection p))) ≫ fixedApexConeHomComparison d x) := by
  simpa only [fixedApexConeHomComparison, Category.assoc] using
    FunctorIso.postcomp (rightFibrationHomComparison_edgeIso (sliceOverProjection p) e x)
      (coneVertexFiberFamilyMap p x)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
