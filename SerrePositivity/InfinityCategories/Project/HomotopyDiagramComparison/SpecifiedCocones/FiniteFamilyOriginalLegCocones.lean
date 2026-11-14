module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.UnitComparisons.FiniteFamilyOriginalProjectionUnit
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.KanExtensions.CoherentTransformationKanCocones

/-!
概要：元の評価全脚の Kan 像の全余錐作用を、頂点比較と元の反復射影の余錐へ移す。
方針：同じ native 辺の単位表示・元の全空間写像余錐・指定単位後の比較を続ける。
規約：元の全脚と同じ有限表示を保持。底の quasicategory 性は要求しない。
使われ方：元の P_Σ 評価錐の脚と、sifted な余極限積錐の全脚の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
variable {B : SSet.{u}} {J : Type u} [Finite J] [Nonempty J]
  (G : J → ((SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}))
  (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFamilyFunctorDiagram G)) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c)
  (A : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
  (hA : c.vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex A)

/-- 元の実際の各評価脚の全空間作用の、元の余極限模型間の Kan 像。 -/
def finiteFamilyOriginalLegKanMap_indexed
    (i : Fin ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteIndexPresentation J).1 + 1)) :=
  let Q := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteIndexPresentation J
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransformationTotalKanMap A (G (Q.2.symm (ULift.up i)))
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFamilyOriginalLegTransformation G c A hA (Q.2.symm (ULift.up i)))

/-- 元の各評価脚の全余錐作用は、元の頂点比較と同じ反復射影の全余錐へ移る。 -/
def finiteFamilyOriginalLegNativeProjectionCoconeIso_indexed
    (i : Fin ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteIndexPresentation J).1 + 1)) :
    let Q := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteIndexPresentation J
    let F := fun k ↦ G (Q.2.symm (ULift.up k))
    let m := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentTransformationTotalMap A (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFamilyCoherentProduct G)
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFamilyConeApexTransformation G c hc A hA) ≫
        _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCoherentSpaceProductTotalProjection Q.1 F i
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (X := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace A (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalVertex (F i)))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePointHomFamily (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalCocone A)
        (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalVertex (F i))).app (Opposite.op ⦋0⦌)
          (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.totalKanNativeHomPoint A (F i) (finiteFamilyOriginalLegKanMap_indexed G c A hA i)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeMappingPointAt (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentTotalMapCocone A (F i) m)
        (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalVertex (F i)) (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentTotalMapCocone_vertex A (F i) m)) := by
  let Q := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteIndexPresentation J
  let F := fun k ↦ G (Q.2.symm (ULift.up k))
  let t := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFamilyOriginalLegTransformation G c A hA (Q.2.symm (ULift.up i))
  let a := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentTransformationTotalMap A (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFamilyCoherentProduct G)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFamilyConeApexTransformation G c hc A hA)
  let m := a ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCoherentSpaceProductTotalProjection Q.1 F i
  have e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentTransformationTotalMap A (F i) t ≫
      _root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalUnit (F i)) (m ≫ _root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalUnit (F i)) :=
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFamilyOriginalProjectionUnitIso_indexed G c hc A hA i)
      rfl (Category.assoc _ _ _).symm
  exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransformationTotalKanNativeCoconeIso A (F i) t ≪≫
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.totalKanMapCoconeIso A (F i) (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentTransformationTotalMap A (F i) t)
      (SSet.RelativeMorphism.Homotopy.refl _) ≪≫
        _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.constantCoconeHomotopyIso A (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalVertex (F i)) e.simplicialHomotopy

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
