module
public import SerrePositivity.KST.SConstruction.PointedKanDiagramEquivalences
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.EdgeEquiv

/-! # 点つき coherent な図式の変換から実際の成分を回収する
概要：入力図式全体の円柱の各対象で、元の Kan 模型間の実際の点つき射を取り出す。
方針：coherent nerve の頂点・辺の既存の厳密な復元を使う。
規約：回収する辺の一単体を保持し、既存の strict な変換の成分も厳密に回収する。
使われ方：全射列の coherent な構造射と、元の選択構造射の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open Spectra
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 全体の円柱の対象 i での辺を、元の Kan 対象を両端に持つ辺として読む。 -/
def pointedKanDiagramHomotopyEdgeAt {I : Type u} [SmallCategory I]
    {F G : I ⥤ PointedSimplicialSet.{u}}
    (hF : ∀ i, KanComplex (F.obj i).right) (hG : ∀ i, KanComplex (G.obj i).right)
    (H : SSet.Homotopy (pointedKanCoherentDiagram F hF) (pointedKanCoherentDiagram G hG))
    (i : I) : PointedKanInfinity.{u}.Edge
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex ((pointedKanDiagram F hF).obj i))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex ((pointedKanDiagram G hG).obj i)) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i))).ofEq
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram_vertex (pointedKanDiagram F hF) i)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram_vertex (pointedKanDiagram G hG) i)

/-- 全体の円柱の対象ごとの辺が表す、元の模型間の実際の点つき射。 -/
def pointedKanDiagramHomotopyMapAt {I : Type u} [SmallCategory I]
    {F G : I ⥤ PointedSimplicialSet.{u}}
    (hF : ∀ i, KanComplex (F.obj i).right) (hG : ∀ i, KanComplex (G.obj i).right)
    (H : SSet.Homotopy (pointedKanCoherentDiagram F hF) (pointedKanCoherentDiagram G hG))
    (i : I) : F.obj i ⟶ G.obj i :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdgeToHom (pointedKanDiagramHomotopyEdgeAt hF hG H i)).hom

/-- 回収した点つき射の辺は、全体の円柱を対象で評価した辺と同じ一単体。 -/
lemma pointedKanDiagramHomotopyMapAt_edge {I : Type u} [SmallCategory I]
    {F G : I ⥤ PointedSimplicialSet.{u}}
    (hF : ∀ i, KanComplex (F.obj i).right) (hG : ∀ i, KanComplex (G.obj i).right)
    (H : SSet.Homotopy (pointedKanCoherentDiagram F hF) (pointedKanCoherentDiagram G hG))
    (i : I) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (show (pointedKanDiagram F hF).obj i ⟶
      (pointedKanDiagram G hG).obj i from
        ObjectProperty.homMk (pointedKanDiagramHomotopyMapAt hF hG H i))).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i))).edge := by
  have he := congrArg SSet.Edge.edge
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge_hom (pointedKanDiagramHomotopyEdgeAt hF hG H i))
  exact he

/-- strict な元の変換を円柱にして成分を戻すと、元の射そのもの。 -/
lemma pointedKanDiagramHomotopyMapAt_natTrans {I : Type u} [SmallCategory I]
    {F G : I ⥤ PointedSimplicialSet.{u}}
    (hF : ∀ i, KanComplex (F.obj i).right) (hG : ∀ i, KanComplex (G.obj i).right)
    (η : F ⟶ G) (i : I) :
    pointedKanDiagramHomotopyMapAt hF hG (pointedKanDiagramHomotopy hF hG η) i = η.app i := by
  let e := pointedKanDiagramHomotopyEdgeAt hF hG (pointedKanDiagramHomotopy hF hG η) i
  have he : e = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge ((pointedKanDiagramNatTrans hF hG η).app i) := by
    apply SSet.Edge.ext
    exact StrictDiagramTransformation.component_edge (pointedKanDiagramNatTrans hF hG η) i
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdgeToHom e).hom = η.app i
  rw [he, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdgeToHom_edge]
  rfl

end SerrePositivity.KST.SConstruction
