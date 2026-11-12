module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FiniteFamilyOriginalLegCocones
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.TotalKanUnitComparisonReflection

/-!
概要：元の評価脚の Kan 像を、同じ slice 代表の頂点比較と反復射影の Kan 合成へ照合する。
方針：元の全錐の三角形と単位比較を、始域単位の弱同値から同じ Kan 射へ反映する。
規約：同じ元の全脚と頂点比較を保持。底の quasicategory 性は不要。
使われ方：元の全評価脚を持つ余極限の native 有限積錐の極限判定。
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
  (A : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
  (hA : c.vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex A)

/-- 全脚と同じ slice 代表を共有する、元の頂点比較の Kan 像。 -/
def finiteFamilyConeApexKanMap :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransformationTotalKanMap A (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFamilyCoherentProduct G)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFamilyConeApexTransformation G c hc A hA)

/-- 同じ元の頂点比較の Kan 像は、任意の底上でホモトピー同値。 -/
lemma finiteFamilyConeApexKanMap_homotopyEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (finiteFamilyConeApexKanMap G c hc A hA) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentInvertibleTotalKanMap_homotopyEquivalence _ _ _
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFamilyConeApexTransformation_isInvertible G c hc A hA)

/-- 元の実際の評価脚の Kan 像は、同じ頂点比較と同じ反復射影の Kan 合成にホモトピック。 -/
lemma finiteFamilyOriginalLegKanMap_homotopy_indexed
    (i : Fin ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteIndexPresentation J).1 + 1)) :
    let Q := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteIndexPresentation J
    let F := fun k ↦ G (Q.2.symm (ULift.up k))
    Nonempty (SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFamilyOriginalLegKanMap_indexed G c A hA i)
      (finiteFamilyConeApexKanMap G c hc A hA ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCoherentSpaceProductTotalProjection Q.1 F i))) := by
  let Q := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteIndexPresentation J
  let F := fun k ↦ G (Q.2.symm (ULift.up k))
  let a := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentTransformationTotalMap A (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFamilyCoherentProduct G)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFamilyConeApexTransformation G c hc A hA)
  have e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentTransformationTotalMap A (F i)
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFamilyOriginalLegTransformation G c A hA (Q.2.symm (ULift.up i))) ≫
        _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalUnit (F i))
      ((a ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCoherentSpaceProductTotalProjection Q.1 F i) ≫
        _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalUnit (F i)) :=
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFamilyOriginalProjectionUnitIso_indexed G c hc A hA i)
      rfl (Category.assoc _ _ _).symm
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFamilyOriginalLegKanMap_indexed, finiteFamilyConeApexKanMap,
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransformationTotalKanMap, Q, F, a, Functor.map_comp] using
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTotalKanMap_homotopy_of_unitIso A (F i) e

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
