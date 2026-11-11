module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FiniteFamilyProductLegReadback

/-!
概要：元の評価全錐の実際の脚を、元の頂点比較と反復全空間射影の単位表現へ移す。
方針：同じ全錐の合成三角形の比較に、元の積脚の厳密な読み戻しと単位比較を続ける。
規約：元の全脚・有限表示・指定単位を保持。底の quasicategory 性は不要。
使われ方：元の評価全脚の native 余極限作用と、sifted 積錐の元の全脚の比較。
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

/-- 元の実際の評価脚は、元の単位の後で頂点比較と同じ反復全空間射影の合成に同型。 -/
def finiteFamilyOriginalProjectionUnitIso_indexed
    (i : Fin ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteIndexPresentation J).1 + 1)) :
    let Q := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteIndexPresentation J
    let F := fun k ↦ G (Q.2.symm (ULift.up k))
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentTransformationTotalMap A (F i)
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFamilyOriginalLegTransformation G c A hA (Q.2.symm (ULift.up i))) ≫
        _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalUnit (F i))
      (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentTransformationTotalMap A (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFamilyCoherentProduct G)
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFamilyConeApexTransformation G c hc A hA) ≫
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCoherentSpaceProductTotalProjection Q.1 F i ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalUnit (F i)) := by
  let Q := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteIndexPresentation J
  exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFamilyOriginalLegUnitIso G c hc A hA (Q.2.symm (ULift.up i)) ≪≫
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFamilyProductLegUnitIso_indexed G i).precomp
      (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentTransformationTotalMap A (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFamilyCoherentProduct G)
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFamilyConeApexTransformation G c hc A hA))

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
