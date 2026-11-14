module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.CoherentDiagrams.CoherentFullSubcategoryRestriction
public import SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.QuillenCfCollageProjection

/-!
概要：cf 対応圏の区間射影の両端 fiber は、元の対応する段の全充満部分圏の nerve。
方針：区間の頂点式から対象の段を判定し、全充満部分圏への厳密な制限を使う。
規約：fibration 性を仮定しない。使われ方：HTT 5.2.4.6 の両端圏の同定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions
noncomputable section
variable {C : Type v} [Category.{u} C] [SimplicialCategory C]
variable {D : Type v} [Category.{u} D] [SimplicialCategory D]
  [HomotopicalAlgebra.ModelCategory C] [HomotopicalAlgebra.ModelCategory D]
  (R : EnrichedFunctor SSet.{u} D C)
/-- 区間の指定された段に属する元の cf 対応圏の対象の条件。 -/
def quillenCfEndpointObjects (i : Fin 2) : ObjectProperty (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.QuillenCfCollage R) :=
  fun X ↦ (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageLevelFunctor R).obj X = ULift.up i

/-- 元の cf 対応圏の指定された段の全充満部分圏。 -/
abbrev QuillenCfEndpointCategory (i : Fin 2) :=
  ObjectProperty.FullSubcategory (quillenCfEndpointObjects R i)

/-- 区間射影の頂点条件と、元の対象が指定段に属する条件の同値。 -/
lemma quillenCfCollageProjection_vertex_eq_iff (X : _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.QuillenCfCollage R) (i : Fin 2) :
    (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageProjection R).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X) =
      stdSimplex.obj₀Equiv.symm i ↔ quillenCfEndpointObjects R i X := by
  rw [_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageProjection_vertex]
  rcases X with ⟨X, hX⟩
  rcases X with X | X <;> constructor
  all_goals intro h
  · exact congrArg ULift.up (stdSimplex.obj₀Equiv.symm.injective h)
  · exact congrArg stdSimplex.obj₀Equiv.symm (congrArg ULift.down h)
  · exact congrArg ULift.up (stdSimplex.obj₀Equiv.symm.injective h)
  · exact congrArg stdSimplex.obj₀Equiv.symm (congrArg ULift.down h)

/-- 指定段の部分圏の nerve は、区間射影の同じ端点上にある。 -/
lemma quillenCfEndpointInclusion_projection (i : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentFullSubcategoryInclusion (quillenCfEndpointObjects R i) ≫
      _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageProjection R = SSet.const (stdSimplex.obj₀Equiv.symm i) := by
  apply (cancel_mono (stdSimplex.isoNerve 1).hom).1
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.thinNerve_hom_ext_vertices
  apply ConcreteCategory.hom_ext
  intro x
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex_object x]
  change (stdSimplex.isoNerve 1).hom.app _ ((_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageProjection R).app _
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.enrichedFullSubcategoryInclusion _)).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex _))) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_vertex]
  exact congrArg (fun y ↦ (stdSimplex.isoNerve 1).hom.app (Opposite.op ⦋0⦌) y)
    ((quillenCfCollageProjection_vertex_eq_iff R _ i).2 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject x).property)

/-- 指定段の部分圏の nerve と、元の区間射影の端点 fiber の同型。 -/
def quillenCfEndpointFiberIso (i : Fin 2) :
    SimplicialNerve (QuillenCfEndpointCategory R i) ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageProjection R) (stdSimplex.obj₀Equiv.symm i) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentFullSubcategoryFiberIso (quillenCfEndpointObjects R i) _ _
    (quillenCfEndpointInclusion_projection R i)
    (fun X h ↦ (quillenCfCollageProjection_vertex_eq_iff R X i).1 h)

/-- 指定段の fiber 同型は元の全空間への包含を保持する。 -/
lemma quillenCfEndpointFiberIso_hom_ι (i : Fin 2) :
    (quillenCfEndpointFiberIso R i).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageProjection R) (stdSimplex.obj₀Equiv.symm i) =
        _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentFullSubcategoryInclusion (quillenCfEndpointObjects R i) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentFullSubcategoryFiberIso_hom_ι _ _ _ _ _

end
end SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions
