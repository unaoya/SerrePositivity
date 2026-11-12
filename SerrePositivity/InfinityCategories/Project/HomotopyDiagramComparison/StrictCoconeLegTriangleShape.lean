module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeLegTriangleShape

/-!
概要：strict な通常図式の射と余錐の実際の二脚の合成二単体を切り出す join 形状。
方針：元の持ち上げた nerve の辺を保持し、既存の strict 合成二単体と照合する。
規約：元の二単体の simplex を保持。使われ方：native span の左右の普遍二単体族。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {I : Type u} [Category.{u} I] {i j : I} (f : i ⟶ j)

/-- 元の通常図式の射を、同じ持ち上げた nerve の実際の辺で表示する。 -/
def strictCoconeShapeEdge : ((SSet.uliftFunctor.{v, u}).obj (nerve I)).Edge
    (ULift.up (ComposableArrows.mk₀ i)) (ULift.up (ComposableArrows.mk₀ j)) :=
  ⟨ULift.up (nerve.edgeMk f).edge, congrArg ULift.up (nerve.edgeMk f).src_eq,
    congrArg ULift.up (nerve.edgeMk f).tgt_eq⟩

/-- 元の strict 図式の射と余錐頂点を join して、実際の二単体を切り出す。 -/
def strictCoconeLegTriangleShape : (Δ[2] : SSet.{max u v}) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join ((SSet.uliftFunctor.{v, u}).obj (nerve I)) Δ[0] :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeLegTriangleShape (strictCoconeShapeEdge f)

/-- 元の strict な合成二単体の最後の頂点は、同じ余錐頂点の右包含である。 -/
lemma strictCoconeLegTriangleShape_tip :
    (stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (0 : Fin 3)) ≫
        strictCoconeLegTriangleShape.{u, v} f =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr ((SSet.uliftFunctor.{v, u}).obj (nerve I)) Δ[0] :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeLegTriangleShape_tip (strictCoconeShapeEdge f)

/-- 実際の join 形状を strict 余錐へ写すと、元の指定した合成二単体そのものになる。 -/
lemma strictCoconeLegTriangleShape_diagram {C : Type v} [Category.{u} C]
    [SimplicialCategory C] (F : I ⥤ C) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F))
    {z₀ z₁ : (SimplicialNerve C) _⦋0⦌}
    (h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (F.obj i) = z₀) (h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (F.obj j) = z₁)
    (k : (SimplicialNerve C).Edge z₀ z₁)
    (hk : k.edge = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (F.map f)).edge) :
    strictCoconeLegTriangleShape f ≫ c.val =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictCoconeVertexLegCompStruct F c f h₀ h₁ k hk).simplex :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeLegTriangleShape_normalized_diagram (strictCoconeShapeEdge f) c
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram_vertex F i).trans h₀) ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram_vertex F j).trans h₁)
    k (hk.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictCoherentDiagram_edge F f).symm)

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
