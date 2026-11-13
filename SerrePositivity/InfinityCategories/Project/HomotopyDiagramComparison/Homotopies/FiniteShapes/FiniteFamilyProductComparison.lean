module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FunctorComparison.FiniteFamilyFunctorProduct
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.NativeConeFamilyEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalUniqueness

/-!
概要：元の関手族上の任意の元の極限錐を、元の反復積関手の全錐へ比較する。
方針：元の slice 内の終対象の一意性を使い、全錐と頂点関手への両作用を保持する。
規約：元の比較元の全錐と元の底図式を保持。元の錐の極限性は明示的な証明を要求する。
使われ方：各前層で評価した元の極限錐の族と sifted 積比較の接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
variable {B : SSet.{u}} {J : Type u} [Finite J] [Nonempty J]
  (G : J → ((SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}))
  (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFamilyFunctorDiagram G)) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c)

/-- 元の関手図式上の元の極限錐と、元の反復積全錐の、同じ slice 内の比較。 -/
def finiteFamilyFunctorProductConeComparison :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFamilyFunctorDiagram G)) c
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFamilyFunctorProductCone G) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.terminalVertexIso hc (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFamilyFunctorProductCone_isLimit G)

/-- 元の slice 比較は、元の全錐の全関手の間の同型を与える。 -/
def finiteFamilyFunctorProductWholeConeIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso c.val (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFamilyFunctorProductCone G).val := by
  have e := (finiteFamilyFunctorProductConeComparison G c hc).map
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeConeFunctorFamily (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFamilyFunctorDiagram G))
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeConeFunctorFamily_vertex, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nativeConeFunctorFamily_vertex] at e
  exact e

/-- 元の全錐の頂点関手は、元の反復積関手と coherent に同型。 -/
def finiteFamilyFunctorProductApexIso
    (A : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (hA : c.vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex A) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso A (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFamilyCoherentProduct G) := by
  have e := (finiteFamilyFunctorProductConeComparison G c hc).map
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFamilyFunctorDiagram G))
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso c.vertex (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFamilyFunctorProductCone G).vertex at e
  rw [hA, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFamilyFunctorProductCone_vertex] at e
  exact e

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
