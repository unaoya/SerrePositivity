module

public import SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetSectionsLimitNaturality
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.FixedApexConeEdgeComparison

/-!
概要：G8 の元の固定端点の錐の比較は、指定錐の辺の標準後合成と全族で可換。
方針：元の固定頂点比較の同型を、同じ固定端点模型の同型で後合成する。
規約：極限性は不要。使われ方：指定極限への写像の全族比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories
open TheSliceAndJoinConstructions MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
open SerrePositivity.InfinityCategories.Project.SetWeightedTensors

namespace SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories

/-- 概要：元の固定端点比較は、同じ指定錐の辺の標準後合成に全自然。
方針：固定頂点の比較の辺の同型を、元の固定端点の同型で後合成する。
規約：元の比較を変更しない。使われ方：G8 の錐の族から極限への写像への接続。 -/
def setWeightLimitConeEndpointComparison_edgeIso {K X : SSet.{u}} [Quasicategory X]
    {p : K ⟶ X} {c d : JoinCone p} (e : (sliceOver p).Edge c d) (x : X _⦋0⦌) :
    FunctorIso (SetWeight.limitConeEndpointComparison c x)
      (postcompose x (SSet.Truncated.HomotopyCategory.homMk (e.map (sliceOverProjection p))) ≫
        SetWeight.limitConeEndpointComparison d x) := by
  simpa only [SetWeight.limitConeEndpointComparison, Category.assoc] using
    FunctorIso.postcomp (fixedApexConeHomComparison_edgeIso e x)
      (fixedApexEndpointConeSpaceIso p x).hom

end SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories
