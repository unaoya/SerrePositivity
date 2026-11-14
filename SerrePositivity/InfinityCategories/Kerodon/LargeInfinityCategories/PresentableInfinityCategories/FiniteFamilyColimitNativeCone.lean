module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Equivalence
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoreLimit
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanDiagramCoherentNerve
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.Vertices
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.KanNativeConeLeg
public import SerrePositivity.InfinityCategories.HTT.Section3_3_4.CoherentTotalObject
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SiftedInfinity
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FunctorComparison.FiniteFamilyFunctorProduct
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FiniteFamilyOriginalColimitTransport
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.FiniteFamilyOriginalLegCocones
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.FiniteFamilyProductCone
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FiniteFamilyTransportedLegComparison
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.KanExtensions.FiniteKanProductNative
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.KanExtensions.KanDiscreteNativeConeOfLegs
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.FiniteShapes.NativeDiscreteLegHomotopy

/-!
概要：元の評価全錐の実際の全脚の Kan 像を持つ余極限全錐が、sifted な底で極限錐。
方針：元の全脚を変更せず native 錐を作り、同じ頂点で輸送した積錐との脚比較で判定する。
規約：元の全脚と余極限頂点を保持。底の quasicategory 性は不要。
使われ方：P_Σ の元の有限錐の像の極限性を元の全脚で回収する。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
variable {B : SSet.{u}} {J : Type u} [Finite J] [Nonempty J]
  (G : J → ((SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}))
  (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFamilyFunctorDiagram G))
  (A : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
  (hA : c.vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex A)

/-- 元の評価全脚の Kan 像をそのまま持つ、元の余極限頂点からの全錐。 -/
def finiteFamilyOriginalColimitNativeCone :
    let Q := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteIndexPresentation J
    let F := fun k ↦ G (Q.2.symm (ULift.up k))
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteKanProductDiagram Q.1 (fun k ↦ _root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalKanObject (F k)))) :=
  let Q := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteIndexPresentation J
  let F := fun k ↦ G (Q.2.symm (ULift.up k))
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanDiscreteNativeConeOfLegs
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteKanProductDiagram Q.1 (fun k ↦ _root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalKanObject (F k)))
    (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalKanObject A)
    (fun i ↦ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFamilyOriginalLegKanMap_indexed G c A hA i.as.down)

/-- 元の全錐の頂点は、元の評価錐頂点の余極限 Kan 模型。 -/
lemma finiteFamilyOriginalColimitNativeCone_vertex :
    (finiteFamilyOriginalColimitNativeCone G c A hA).vertex =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalKanObject A) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanDiscreteNativeConeOfLegs_vertex _ _ _

/-- 元の全錐の全脚は、元の実際の評価全脚の Kan 像そのもの。 -/
lemma finiteFamilyOriginalColimitNativeCone_kanLeg
    (i : Discrete (ULift.{u} (Fin ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteIndexPresentation J).1 + 1)))) :
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.kanNativeConeLeg (finiteFamilyOriginalColimitNativeCone G c A hA)
      (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalKanObject A)
      (finiteFamilyOriginalColimitNativeCone_vertex G c A hA) i =
        _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFamilyOriginalLegKanMap_indexed G c A hA i.as.down :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanDiscreteNativeConeOfLegs_kanLeg _ _ _ i

/-- sifted な任意の底上で、元の全評価脚の Kan 像を持つ同じ全錐は極限錐。 -/
lemma finiteFamilyOriginalColimitNativeCone_isLimit [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.IsSiftedInfinity B] (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (finiteFamilyOriginalColimitNativeCone G c A hA) := by
  apply (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.discreteSpaceCone_isLimit_iff_of_leg_homotopies _
    (finiteFamilyOriginalColimitNativeCone G c A hA)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.finiteFamilyOriginalColimitTransportedCone G c hc A hA)
    (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalKanObject A) (finiteFamilyOriginalColimitNativeCone_vertex G c A hA)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.finiteFamilyOriginalColimitTransportedCone_vertex G c hc A hA) (fun i ↦ ?_)).mpr
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.finiteFamilyOriginalColimitTransportedCone_isLimit G c hc A hA)
  rw [finiteFamilyOriginalColimitNativeCone_kanLeg]
  exact Classical.choice (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.finiteFamilyOriginalLegKanMap_transported G c hc A hA i)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
