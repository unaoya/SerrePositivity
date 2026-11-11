module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.PartialColimitSpanTriangles
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitAttachmentTransportIso

/-!
概要：span の普遍余錐の元の二単体から、輸送した二つの部分余錐の境界を結ぶ指定経路を作る。
方針：制限の輸送自然性、実際の付加比較辺、左右の三角形の輸送比較を合成する。
規約：任意の π₀ の一致から経路を選ばない。使われ方：指定経路を保つ貼り合わせへの入力。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {A B C : SSet.{u + 1}} {p : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}}
  (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c)
  (i : A ⟶ B) (F : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) (hi : i ≫ F = p) (dB : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone F)
  (j : A ⟶ C) (G : C ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) (hj : j ≫ G = p) (dC : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone G)

/-- 元の二単体と付加比較辺により指定された、右境界から左境界への点図式の同型。 -/
def partialColimitSpanBoundaryIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.transportedCoconeVertex dC
          (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRightLeg c hc i F hi dB j G hj dC)) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber G j hj
          (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitStrictSpanCocone c hc i F hi dB j G hj dC).vertex)
      (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.transportedCoconeVertex dB
          (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanLeftLeg c hc i F hi dB j G hj dC)) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber F i hi
          (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitStrictSpanCocone c hc i F hi dB j G hj dC).vertex) := by
  let eB := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanLeftLeg c hc i F hi dB j G hj dC
  let eC := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRightLeg c hc i F hi dB j G hj dC
  let q := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p
  let v := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialFiberVertexAt q c c.vertex rfl
  have AB : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitAttachmentFiberVertex i F hi dB) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport q eB)
      (SSet.yonedaEquiv.symm v ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport q (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitAttachmentApexEdge c hc i F hi dB) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport q eB)) := by
    simpa only [Category.assoc] using _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitAttachmentTransportPointIso c hc i F hi dB) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport q eB)
  have AC : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitAttachmentFiberVertex j G hj dC) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport q eC)
      (SSet.yonedaEquiv.symm v ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport q (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitAttachmentApexEdge c hc j G hj dC) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport q eC)) := by
    simpa only [Category.assoc] using _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitAttachmentTransportPointIso c hc j G hj dC) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport q eC)
  let M := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanTransportIso c hc i F hi dB j G hj dC q) (SSet.yonedaEquiv.symm v)
  exact ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeBoundaryTransportPointIso i F hi dB eB) ≪≫ AB ≪≫ M ≪≫ AC.symm ≪≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeBoundaryTransportPointIso j G hj dC eC).symm).symm

/-- span の普遍余錐が指定する、実際の右境界から左境界への可逆経路。 -/
def partialColimitSpanBoundaryPath :
    (Δ[0] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePath
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace p (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitStrictSpanCocone c hc i F hi dB j G hj dC).vertex) :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.homotopyEquivalencePath
    (partialColimitSpanBoundaryIso c hc i F hi dB j G hj dC).simplicialHomotopy

/-- 指定した経路の始点は、右部分余錐を実際の右脚で輸送した余錐の境界。 -/
lemma partialColimitSpanBoundaryPath_zero :
    partialColimitSpanBoundaryPath c hc i F hi dB j G hj dC ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint _ 0 =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.transportedCoconeVertex dC
          (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRightLeg c hc i F hi dB j G hj dC)) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber G j hj
          (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitStrictSpanCocone c hc i F hi dB j G hj dC).vertex :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.homotopyEquivalencePath_zero _

/-- 指定した経路の終点は、左部分余錐を実際の左脚で輸送した余錐の境界。 -/
lemma partialColimitSpanBoundaryPath_one :
    partialColimitSpanBoundaryPath c hc i F hi dB j G hj dC ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint _ 1 =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.transportedCoconeVertex dB
          (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanLeftLeg c hc i F hi dB j G hj dC)) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber F i hi
          (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitStrictSpanCocone c hc i F hi dB j G hj dC).vertex :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.homotopyEquivalencePath_one _

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
