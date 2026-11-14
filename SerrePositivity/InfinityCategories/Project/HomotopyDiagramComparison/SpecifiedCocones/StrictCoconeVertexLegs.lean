module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeVertexLegNormalization
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CosliceTransport

/-!
概要：通常の図式の coherent 余錐の脚を指定した頂点で表し、実際の射との三角形を計算する。
方針：通常の nerve の辺を持ち上げ、strict 図式の辺の評価式を適用する。
規約：Hom の宇宙と対象の宇宙は異なってよい。使われ方：部分余極限頂点の span の余錐。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {I : Type u} [Category.{u} I] {C : Type v} [Category.{u} C]
  [SimplicialCategory C] (F : I ⥤ C) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F))

/-- 通常の添字対象の像と等しい、指定した始点からの余錐の脚。 -/
def strictCoconeVertexLeg (i : I) (z : (SimplicialNerve C) _⦋0⦌)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (F.obj i) = z) : (SimplicialNerve C).Edge z c.vertex :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeVertexLegAt c (ULift.up (ComposableArrows.mk₀ i)) z
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram_vertex F i).trans h)

/-- 通常の射の coherent な辺と一致する実際の辺は、指定始点での余錐の二脚と可換。 -/
lemma strictCoconeVertexLeg_comp {i j : I} (f : i ⟶ j)
    {z₀ z₁ : (SimplicialNerve C) _⦋0⦌}
    (h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (F.obj i) = z₀)
    (h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (F.obj j) = z₁)
    (k : (SimplicialNerve C).Edge z₀ z₁)
    (hk : k.edge = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (F.map f)).edge) :
    SSet.Truncated.HomotopyCategory.homMk k.toTruncated ≫
        SSet.Truncated.HomotopyCategory.homMk (strictCoconeVertexLeg F c j z₁ h₁).toTruncated =
      SSet.Truncated.HomotopyCategory.homMk (strictCoconeVertexLeg F c i z₀ h₀).toTruncated := by
  let e : ((SSet.uliftFunctor.{v, u}).obj (nerve I)).Edge
      (ULift.up (ComposableArrows.mk₀ i)) (ULift.up (ComposableArrows.mk₀ j)) :=
    ⟨ULift.up (nerve.edgeMk f).edge,
      congrArg ULift.up (nerve.edgeMk f).src_eq,
      congrArg ULift.up (nerve.edgeMk f).tgt_eq⟩
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeVertexLegAt_comp c e
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram_vertex F i).trans h₀)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram_vertex F j).trans h₁) k
  exact hk.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictCoherentDiagram_edge F f).symm

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
