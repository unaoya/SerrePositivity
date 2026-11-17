module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedHomInterval
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagramOrdinaryAction
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.HomIntervalVertices
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.JointComparisonPrecomposition
/-!
概要：豊穣Homの指定頂点から作る区間辺を、同じcoherentな辺の実現へ同定する。
方針：既存のHom区間比較の頂点公式と、端点を正規化したHom作用を使う。
規約：HTT §1.1.5、Kerodon §2.4.3・§3.1の構成の評価法則。
  局所Kan性や新たな図式の同値を仮定せず、指定頂点と指定辺を保つ特殊化。
使われ方：5∞-1のP3-C1PNで、元の反転Hom区間の射の類を読む。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans

namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes

/-- 豊穣Homの同じ頂点から得た区間辺は、元のcoherent辺の実現そのもの。 -/
lemma kanEnrichedDiagramHomInterval_vertex {C : Type (u+1)} [Category.{u} C] [SimplicialCategory C]
    {I : Type u} [SmallCategory I] (D : KanEnrichedDiagram C I) (X Y : C)
    (s : (SimplicialCategory.sHom X Y) _⦋0⦌) :
    intervalMappingEdgeOfVertex
      ((kanEnrichedDiagramHomInterval D X Y rfl rfl).app _ (ULift.up s)) =
    ((coherentNerveEdge ((SimplicialCategory.homEquiv' X Y).symm s)).map D.realization).ofEq
      (D.realization_vertex X) (D.realization_vertex Y) := by
  change intervalMappingEdgeOfVertex
    ((intervalMappingPostOfEq D.realization (coherentNerveVertex X) (coherentNerveVertex Y)
      (D.realization_vertex X) (D.realization_vertex Y)).app _
        ((coherentHomIntervalComparison X Y).app _ (ULift.up s))) = _
  rw [coherentHomIntervalComparison_vertex, intervalMappingPostOfEq_vertex]
  exact (intervalMappingEdgeVertexEquiv _ _).symm_apply_apply _

/-- 同じ区間辺の射の類は、実現の正規化したHom作用。 -/
@[cite HTT "1.1.5" (partial := special) "豊穣Homの指定頂点におけるcoherent実現の評価法則。"]
lemma kanEnrichedDiagramHomInterval_vertex_hom {C : Type (u+1)} [Category.{u} C] [SimplicialCategory C]
    {I : Type u} [SmallCategory I] (D : KanEnrichedDiagram C I) (X Y : C)
    (s : (SimplicialCategory.sHom X Y) _⦋0⦌) :
    Truncated.HomotopyCategory.homMk
      (intervalMappingEdgeOfVertex
        ((kanEnrichedDiagramHomInterval D X Y rfl rfl).app _ (ULift.up s))).toTruncated =
    normalizedVertexHomMap D.realization (D.realization_vertex X).symm (D.realization_vertex Y).symm
      (Truncated.HomotopyCategory.homMk
        (coherentNerveEdge ((SimplicialCategory.homEquiv' X Y).symm s)).toTruncated) := by
  rw [kanEnrichedDiagramHomInterval_vertex]
  exact (normalizedVertexHomMap_homMk D.realization (D.realization_vertex X).symm
    (D.realization_vertex Y).symm _).symm

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
