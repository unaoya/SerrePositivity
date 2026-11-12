module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramOrdinaryEdgeSimplex
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity.StrictCoherentNatTrans
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.FunctorFamilyPrism

/-!
概要：元の Kan 図式の自然変換の辺の prism を、通常の区間図式の prism と同定する。
方針：任意の次数で、底の射列と区間の単体の対角評価の公式を適用する。
規約：端点だけでなく、実際の辺の Yoneda 射の全評価を比較する。
使われ方：G8 の要素の圏の pointed 区間族の底を、元の spaceDiagramEdge にそろえる。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity

/-- 元の実現した自然変換の辺の全 prism は、同じ通常の自然変換の coherent prism である。 -/
lemma kanDiagramNaturalTransformationEdge_prism {C : Type u} [SmallCategory C]
    {F G : KanDiagramObject C}
    (η : F.val ⋙ kanObjectForget ⟶ G.val ⋙ kanObjectForget) :
    functorEdgePrism (kanDiagramNaturalTransformationEdge η) =
      strictCoherentNatTransMap (kanDiagramUnderlyingTransformation η) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  change kanDiagramDiagonalSimplex s.2.down
      ((KanDiagramNerve C).map (stdSimplex.objEquiv s.1).op
        (coherentNerveEdge (kanDiagramHom η)).edge) =
    enrichedFunctorOfOrderDiagram (kanDiagramEdgeOrderDiagram η s.2.down
      (stdSimplex.objEquiv s.1))
  exact kanDiagramDiagonalSimplex_edge η s.2.down (stdSimplex.objEquiv s.1)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
