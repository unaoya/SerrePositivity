module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LoopConeFixedApexSourceLift
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LoopCommaInitialArrow

/-!
概要：元の普遍 loop 錐の指定点の始対象性と、同じ零隅四角形への移送。
方針：固定 cospan の終対象の自己比較と、実 classifier・選択忘却を接続する。
規約：最後の全四角形図式を厳密に保つ。使われ方：同じ loop 四角形の押し出し性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 元の普遍 loop 錐の同じ指定点と四角形を保つ比較。 -/
lemma loopConeUniversalSourcePoint_isInitial {X : SSet.{u}} [Quasicategory X]
    [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex X] (s : X ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams X)
    (hs : s ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 1 1 = 𝟙 X)
    (hΩ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (s ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 0 0))
    {y : X _⦋0⦌} (t : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LoopSquare y) :
    let x := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneFamilyApex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan t.square)).app
      (Opposite.op ⦋0⦌) ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.sliceConeFamilyMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan t.square)).app
        (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone t.square))
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeFixedApexSourceLift t x).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeUniversalFixedApexPoint t)) := by
  let p := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan t.square
  let c := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.sliceConeFamilyMap p).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone t.square)
  let x := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneFamilyApex p).app (Opposite.op ⦋0⦌) c
  let v := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeUniversalFixedApexPoint t
  let L := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeFixedApexLift t x
  let f := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeFixedApexSourceLift t x ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeClassifierSourceFiberMap X x
  have hh := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeFixedApexSourceLift_classifier_h t x
  have hid : L.app (Opposite.op ⦋1⦌)
      (SSet.Truncated.Edge.id (X := (truncation 2).obj
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedApexConeFamily p x)) v).edge =
      (SSet.Truncated.Edge.id (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeObjects X))
        (L.app (Opposite.op ⦋0⦌) v)).edge :=
    ConcreteCategory.congr_hom (L.naturality (SimplexCategory.σ (0 : Fin 1)).op) v
  have hraw := congrArg (fun q ↦ q.app (Opposite.op ⦋1⦌)
    ((SSet.Truncated.Edge.id (X := (truncation 2).obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedApexConeFamily p x)) v).edge, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge)) hh
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberHomotopy f).h.app (Opposite.op ⦋1⦌)
      ((SSet.Truncated.Edge.id (X := (truncation 2).obj
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedApexConeFamily p x)) v).edge, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge) =
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeApexComparisonHomotopy X).h.app (Opposite.op ⦋1⦌)
      (L.app (Opposite.op ⦋1⦌)
        (SSet.Truncated.Edge.id (X := (truncation 2).obj
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedApexConeFamily p x)) v).edge, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge) at hraw
  rw [hid] at hraw
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberHomotopy f) v).toTruncated :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr hraw).mpr (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeUniversalApexComparison_isInvertible t)
  have ha := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.unitCommaFiberArrowHom_isIso_of_family_vertexEdge f v he
  have hi := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopUnitCommaFiber_isInitial_iff_invertibleArrow s hs hΩ x
    (f.app (Opposite.op ⦋0⦌) v)).mpr ha
  let e := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeClassifierSourceFiberMap_isQCatEquivalence X x).choose
  exact (e.isInitialVertex_iff
    ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeFixedApexSourceLift t x).app (Opposite.op ⦋0⦌) v)).mpr hi
end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
