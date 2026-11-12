module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FiniteFamilyConeUnitComparison
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FiniteCoherentProjection

/-!
概要：元の一般有限積全錐の実際の脚を、同じ有限表示の反復射影変換と厳密に照合する。
方針：元の脚の全一単体と区間頂点・辺の往復を使い、元の有限表示を保持する。
規約：全空間作用や単位の比較へ移る前に、変換頂点そのものを等式で回収する。
使われ方：元の評価全錐の全脚と、sifted な余極限積錐の反復射影の接続。
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

/-- 元の一般有限積の同じ実際の脚は、同じ有限表示の元の反復射影変換そのもの。 -/
lemma finiteFamilyProductLegTransformation_indexed
    (i : Fin ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteIndexPresentation J).1 + 1)) :
    let Q := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteIndexPresentation J
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFamilyProductLegTransformation G (Q.2.symm (ULift.up i)) =
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCoherentProjectionVertex Q.1 (fun k ↦ G (Q.2.symm (ULift.up k))) i := by
  let Q := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteIndexPresentation J
  let F := fun k ↦ G (Q.2.symm (ULift.up k))
  have he : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFamilyProductConeLeg G (Q.2.symm (ULift.up i)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeOfVertex (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCoherentProjectionVertex Q.1 F i) := by
    apply SSet.Edge.ext
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFamilyFunctorProductCone G)
      (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Discrete.mk (Q.2.symm (ULift.up i)))))).edge = _
    have h := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFamilyFunctorProductCone_leg_edge G (Q.2.symm (ULift.up i))
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFamilyFunctorProductCone G)
      (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Discrete.mk (Q.2.symm (ULift.up i)))))).edge =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeOfVertex (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCoherentProjectionVertex Q.1 F
          (Q.2 (Q.2.symm (ULift.up i))).down)).edge at h
    have hi : (Q.2 (Q.2.symm (ULift.up i))).down = i :=
      congrArg ULift.down (Q.2.apply_symm_apply (ULift.up i))
    rw [hi] at h
    exact h
  exact (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge he).trans
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeVertexEquiv _ _).apply_symm_apply _)

/-- 元の積脚の全空間作用は、元の単位の後で同じ反復全空間射影に一致する。 -/
def finiteFamilyProductLegUnitIso_indexed
    (i : Fin ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteIndexPresentation J).1 + 1)) :
    let Q := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteIndexPresentation J
    let F := fun k ↦ G (Q.2.symm (ULift.up k))
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentTransformationTotalMap (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFamilyCoherentProduct G) (F i)
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFamilyProductLegTransformation G (Q.2.symm (ULift.up i))) ≫
        _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalUnit (F i))
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCoherentSpaceProductTotalProjection Q.1 F i ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalUnit (F i)) := by
  dsimp only
  rw [finiteFamilyProductLegTransformation_indexed]
  exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCoherentProjectionUnitIso _ _ i

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
