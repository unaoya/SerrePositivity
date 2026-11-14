module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Equivalence
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.EdgeApexPrism
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanHomotopyEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoreLimit
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.PrismContraction
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanDiagramCoherentNerve
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.Edges
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanInvertible
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.Vertices
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.CoherentFilteredTotalDetection
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.KanApexConeTransportEdges
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.SpecifiedApexLimitConeTransport
public import SerrePositivity.InfinityCategories.HTT.Section3_3_4.CoherentTotalObject
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SiftedInfinity
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FiniteCoherentProductNativeCone
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.CoherentDiagrams.FiniteCoherentProductTotalMap
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FunctorComparison.FiniteFamilyFunctorProduct
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.KanExtensions.FiniteFamilyOriginalKanComparison
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.FiniteFamilyProductCone
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.KanExtensions.FiniteKanProductNative
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic

/-!
概要：元の評価錐頂点の余極限を頂点に持つ全積錐を、同じ slice 比較辺で構成する。
方針：元の反復積の余極限全錐を、全脚と共有した同じ頂点比較の Kan 像で輸送する。
規約：元の底図式・頂点辺・全錐円柱を保持。底の quasicategory 性は不要。
使われ方：元の実際の評価脚の Kan 像を持つ積錐の極限性の回収。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
variable {B : SSet.{u}} [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.IsSiftedInfinity B] {J : Type u} [Finite J] [Nonempty J]
  (G : J → ((SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}))
  (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFamilyFunctorDiagram G)) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c)
  (A : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
  (hA : c.vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex A)

/-- 元の同じ頂点比較の Kan 像を、元の Kan 対象間の指定射に束ねる。 -/
def finiteFamilyConeApexKanObjectMap :
    _root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalKanObject A ⟶
      _root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalKanObject (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFamilyCoherentProduct G) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFamilyConeApexKanMap G c hc A hA

/-- 元の余極限積全錐を、全脚と同じ slice 代表から得た辺で頂点輸送する。 -/
def finiteFamilyOriginalColimitConeTransport :
    let Q := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteIndexPresentation J
    let F := fun k ↦ G (Q.2.symm (ULift.up k))
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.SpecifiedApexLimitConeTransport (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.finiteSiftedCoherentProductNativeCone Q.1 F)
      (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalKanObject A)))
      (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.edgeApexPrism (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (finiteFamilyConeApexKanObjectMap G c hc A hA))) := by
  let Q := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteIndexPresentation J
  let F := fun k ↦ G (Q.2.symm (ULift.up k))
  let a := finiteFamilyConeApexKanObjectMap G c hc A hA
  exact _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.specifiedApexLimitConeTransport _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.finiteSiftedCoherentProductNativeCone_isLimit Q.1 F)
    _ _ (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.edgeApexPrism_zero _) (by
      rw [_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.edgeApexPrism_one]
      apply SSet.yonedaEquiv.injective
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.finiteSiftedCoherentProductNativeCone_vertex Q.1 F).symm)
    (fun x ↦ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.edgeApexPrism_vertical_isInvertible _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentKanEdge_isInvertible_of_isQCatEquivalence
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFamilyConeApexKanMap_homotopyEquivalence G c hc A hA).isQCatEquivalence) x)

/-- 元の評価錐頂点の余極限 Kan 模型を頂点に持つ、元の図式上の全積錐。 -/
def finiteFamilyOriginalColimitTransportedCone :=
  (finiteFamilyOriginalColimitConeTransport G c hc A hA).cone

/-- 同じ元の比較辺で輸送した全積錐の頂点は、元の評価錐頂点の余極限。 -/
lemma finiteFamilyOriginalColimitTransportedCone_vertex :
    (finiteFamilyOriginalColimitTransportedCone G c hc A hA).vertex =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalKanObject A) :=
  _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.kanApexConeTransport_vertex _ (finiteFamilyConeApexKanObjectMap G c hc A hA)
    (finiteFamilyOriginalColimitConeTransport G c hc A hA) rfl

/-- 同じ元の全図式を保つ輸送全錐は、元の評価錐頂点の余極限を頂点とする極限錐。 -/
lemma finiteFamilyOriginalColimitTransportedCone_isLimit :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (finiteFamilyOriginalColimitTransportedCone G c hc A hA) :=
  (finiteFamilyOriginalColimitConeTransport G c hc A hA).isLimit

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
