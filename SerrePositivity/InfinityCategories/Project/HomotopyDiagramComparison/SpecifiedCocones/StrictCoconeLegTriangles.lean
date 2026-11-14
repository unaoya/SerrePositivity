module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.StrictCoconeVertexLegs

/-!
概要：通常の図式の coherent 余錐の脚の可換性を、元の二単体を保つ合成三角形として公開する。
方針：元の join による三角形の面を、指定した始点と実際の構造辺へ正規化する。
規約：ホモトピー圏の等式で代用しない。使われ方：span の普遍余錐が指定する境界経路の抽出。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

/-- 指定始点で表示した二脚の可換性を表す、元の実際の合成二単体。 -/
def coconeVertexLegAtCompStruct {K X : SSet.{u}} {p : K ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p)
    {a b : K _⦋0⦌} (e : K.Edge a b) {z₀ z₁ : X _⦋0⦌}
    (h₀ : p.app (Opposite.op ⦋0⦌) a = z₀) (h₁ : p.app (Opposite.op ⦋0⦌) b = z₁)
    (k : X.Edge z₀ z₁) (hk : k.edge = (e.map p).edge) :
    SSet.Edge.CompStruct k (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeVertexLegAt c b z₁ h₁) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeVertexLegAt c a z₀ h₀) := by
  let t := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeVertexLegCompStruct c e
  exact ⟨t.simplex, t.d₂.trans hk.symm, t.d₀, t.d₁⟩

/-- strict な通常の図式の射と余錐の二脚の、実際の合成三角形。 -/
def strictCoconeVertexLegCompStruct {I : Type u} [Category.{u} I]
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (F : I ⥤ C) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F)) {i j : I} (f : i ⟶ j)
    {z₀ z₁ : (SimplicialNerve C) _⦋0⦌}
    (h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (F.obj i) = z₀) (h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (F.obj j) = z₁)
    (k : (SimplicialNerve C).Edge z₀ z₁)
    (hk : k.edge = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (F.map f)).edge) :
    SSet.Edge.CompStruct k (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictCoconeVertexLeg F c j z₁ h₁)
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictCoconeVertexLeg F c i z₀ h₀) := by
  let e : ((SSet.uliftFunctor.{v, u}).obj (nerve I)).Edge
      (ULift.up (ComposableArrows.mk₀ i)) (ULift.up (ComposableArrows.mk₀ j)) :=
    ⟨ULift.up (nerve.edgeMk f).edge,
      congrArg ULift.up (nerve.edgeMk f).src_eq,
      congrArg ULift.up (nerve.edgeMk f).tgt_eq⟩
  exact coconeVertexLegAtCompStruct c e
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram_vertex F i).trans h₀)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram_vertex F j).trans h₁) k
    (hk.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictCoherentDiagram_edge F f).symm)

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
