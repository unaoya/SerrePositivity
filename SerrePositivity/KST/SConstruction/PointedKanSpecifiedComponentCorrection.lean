module
public import SerrePositivity.KST.SConstruction.HomotopySpecifiedVertexCorrection
public import SerrePositivity.KST.SConstruction.PointedKanHomotopyComponents
public import SerrePositivity.KST.SConstruction.PointedKanHomotopyCategoryComparison

/-! # 元の点つき成分を厳密に指定した coherent な図式の変換
概要：同じ点つきホモトピー成分の射の族を、全体変換の成分として厳密に回収する。
方針：coherent nerve の射の類の忠実性を離散頂点の補正定理へ接続する。
規約：元の全体図式・全体変換の射の類を保ち、全対象を同時に補正する。
使われ方：元の BF K の構造射を全射列の変換の縦辺として固定する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalClosed SSet
open Spectra Spectra.PointedMapping
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 任意の底の頂点で coherent な図式は元の Kan 対象を回収する。 -/
lemma pointedKanCoherentDiagram_vertex_any {I : Type u} [SmallCategory I]
    (F : I ⥤ PointedSimplicialSet.{u}) (hF : ∀ i, KanComplex (F.obj i).right)
    (a : ((SSet.uliftFunctor.{u+1,u}).obj (nerve I)) _⦋0⦌) :
    (pointedKanCoherentDiagram F hF).app (Opposite.op ⦋0⦌) a =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex ((pointedKanDiagram F hF).obj (a.down.obj 0)) := by
  rcases a with ⟨s⟩
  have hs : s = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (s.obj 0) := ComposableArrows.ext₀ rfl
  exact (congrArg ((pointedKanCoherentDiagram F hF).app (Opposite.op ⦋0⦌))
    (congrArg ULift.up hs)).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram_vertex (pointedKanDiagram F hF) (s.obj 0))

/-- 離散頂点への制限でも、元の Kan 対象の coherent な頂点を回収する。 -/
lemma pointedKanCoherentDiagram_discrete_vertex {I : Type u} [SmallCategory I]
    (F : I ⥤ PointedSimplicialSet.{u}) (hF : ∀ i, KanComplex (F.obj i).right)
    (a : ((SSet.uliftFunctor.{u+1,u}).obj (nerve I)) _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscreteι ((SSet.uliftFunctor.{u+1,u}).obj (nerve I)) ≫
      pointedKanCoherentDiagram F hF).app (Opposite.op ⦋0⦌) a =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex ((pointedKanDiagram F hF).obj (a.down.obj 0)) := by
  change (pointedKanCoherentDiagram F hF).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant a 0) = _
  exact (congrArg ((pointedKanCoherentDiagram F hF).app (Opposite.op ⦋0⦌))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero a)).trans (pointedKanCoherentDiagram_vertex_any F hF a)

/-- 元の点つき射の族を、離散頂点上の指定した coherent な辺として読む。 -/
def pointedKanDiagramSpecifiedVertexEdge {I : Type u} [SmallCategory I]
    {F G : I ⥤ PointedSimplicialSet.{u}}
    (hF : ∀ i, KanComplex (F.obj i).right) (hG : ∀ i, KanComplex (G.obj i).right)
    (f : ∀ i, F.obj i ⟶ G.obj i)
    (a : ((SSet.uliftFunctor.{u+1,u}).obj (nerve I)) _⦋0⦌) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (show (pointedKanDiagram F hF).obj (a.down.obj 0) ⟶
    (pointedKanDiagram G hG).obj (a.down.obj 0) from ObjectProperty.homMk (f (a.down.obj 0)))).ofEq
    (pointedKanCoherentDiagram_discrete_vertex F hF a).symm
    (pointedKanCoherentDiagram_discrete_vertex G hG a).symm

/-- 元の各対象の射の成分が全体変換の成分と一致すれば、離散部分で同じ射の類になる。 -/
lemma pointedKanDiagramSpecifiedVertexEdge_hom {I : Type u} [SmallCategory I]
    {F G : I ⥤ PointedSimplicialSet.{u}}
    (hF : ∀ i, KanComplex (F.obj i).right) (hG : ∀ i, KanComplex (G.obj i).right)
    (H : SSet.Homotopy (pointedKanCoherentDiagram F hF) (pointedKanCoherentDiagram G hG))
    (f : ∀ i, F.obj i ⟶ G.obj i)
    (hf : ∀ i, componentOf (pointedKanDiagramHomotopyMapAt hF hG H i) = componentOf (f i))
    (a : ((SSet.uliftFunctor.{u+1,u}).obj (nerve I)) _⦋0⦌) :
    SSet.Truncated.HomotopyCategory.homMk
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp H
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscreteι ((SSet.uliftFunctor.{u+1,u}).obj (nerve I))))).map
          ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertexDiscreteEvaluate (A := (SSet.uliftFunctor.{u+1,u}).obj (nerve I))
          (X := PointedKanInfinity.{u}) a))) =
    SSet.Truncated.HomotopyCategory.homMk
      ((vertexDiscreteSpecifiedEdge _ _ (pointedKanDiagramSpecifiedVertexEdge hF hG f)).map
        ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertexDiscreteEvaluate (A := (SSet.uliftFunctor.{u+1,u}).obj (nerve I))
          (X := PointedKanInfinity.{u}) a))) := by
  rcases a with ⟨s⟩
  obtain ⟨i, rfl⟩ : ∃ i, s = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i := ⟨s.obj 0, ComposableArrows.ext₀ rfl⟩
  let a : ((SSet.uliftFunctor.{u+1,u}).obj (nerve I)) _⦋0⦌ := ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i)
  let e := SSet.Edge.ofTruncated (X := PointedKanInfinity.{u})
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp H
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscreteι ((SSet.uliftFunctor.{u+1,u}).obj (nerve I))))).map
        ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertexDiscreteEvaluate (A := (SSet.uliftFunctor.{u+1,u}).obj (nerve I))
          (X := PointedKanInfinity.{u}) a)))
  let k := SSet.Edge.ofTruncated (X := PointedKanInfinity.{u})
    ((vertexDiscreteSpecifiedEdge _ _ (pointedKanDiagramSpecifiedVertexEdge hF hG f)).map
      ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertexDiscreteEvaluate (A := (SSet.uliftFunctor.{u+1,u}).obj (nerve I))
          (X := PointedKanInfinity.{u}) a)))
  let hx := pointedKanCoherentDiagram_discrete_vertex F hF a
  let hy := pointedKanCoherentDiagram_discrete_vertex G hG a
  change SSet.Truncated.HomotopyCategory.homMk e.toTruncated =
    SSet.Truncated.HomotopyCategory.homMk k.toTruncated
  apply (diagramEdge_homMk_ofEq_iff e k hx hy).mp
  have he : e.ofEq hx hy = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge
      (show (pointedKanDiagram F hF).obj i ⟶ (pointedKanDiagram G hG).obj i from
        ObjectProperty.homMk (pointedKanDiagramHomotopyMapAt hF hG H i)) := by
    apply SSet.Edge.ext
    exact (vertexDiscrete_restriction_edge_evaluate H a).trans
      (pointedKanDiagramHomotopyMapAt_edge hF hG H i).symm
  have hk : k.ofEq hx hy = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge
      (show (pointedKanDiagram F hF).obj i ⟶ (pointedKanDiagram G hG).obj i from
        ObjectProperty.homMk (f i)) := by
    apply SSet.Edge.ext
    exact vertexDiscreteSpecifiedEdge_evaluate _ _ (pointedKanDiagramSpecifiedVertexEdge hF hG f) a
  rw [he, hk]
  exact (pointedKanHomotopyClass_eq_iff
    (show (pointedKanDiagram F hF).obj i ⟶ (pointedKanDiagram G hG).obj i from
      ObjectProperty.homMk (pointedKanDiagramHomotopyMapAt hF hG H i))
    (show (pointedKanDiagram F hF).obj i ⟶ (pointedKanDiagram G hG).obj i from
      ObjectProperty.homMk (f i))).mpr (hf i)

/-- 全ての元の点つき成分を厳密に回収し、元の全体変換の射の類を保つ補正が存在する。 -/
lemma exists_pointedKanDiagram_specified_components {I : Type u} [SmallCategory I]
    {F G : I ⥤ PointedSimplicialSet.{u}}
    (hF : ∀ i, KanComplex (F.obj i).right) (hG : ∀ i, KanComplex (G.obj i).right)
    (H : SSet.Homotopy (pointedKanCoherentDiagram F hF) (pointedKanCoherentDiagram G hG))
    (f : ∀ i, F.obj i ⟶ G.obj i)
    (hf : ∀ i, componentOf (pointedKanDiagramHomotopyMapAt hF hG H i) = componentOf (f i)) :
    ∃ H' : SSet.Homotopy (pointedKanCoherentDiagram F hF) (pointedKanCoherentDiagram G hG),
      (∀ i, pointedKanDiagramHomotopyMapAt hF hG H' i = f i) ∧
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H') =
        SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H) := by
  obtain ⟨H', he, hh⟩ := exists_vertexDiscrete_homotopy_correction H
    (pointedKanDiagramSpecifiedVertexEdge hF hG f) (pointedKanDiagramSpecifiedVertexEdge_hom hF hG H f hf)
  refine ⟨H', ?_, hh⟩
  intro i
  have hedge : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge
      (show (pointedKanDiagram F hF).obj i ⟶ (pointedKanDiagram G hG).obj i from
        ObjectProperty.homMk (pointedKanDiagramHomotopyMapAt hF hG H' i)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (show (pointedKanDiagram F hF).obj i ⟶ (pointedKanDiagram G hG).obj i from
        ObjectProperty.homMk (f i)) := by
    apply SSet.Edge.ext
    exact (pointedKanDiagramHomotopyMapAt_edge hF hG H' i).trans (he (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i)))
  have hmaps := congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdgeToHom hedge
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdgeToHom_edge, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdgeToHom_edge] at hmaps
  exact congrArg (fun q : (pointedKanDiagram F hF).obj i ⟶ (pointedKanDiagram G hG).obj i => q.hom) hmaps

end SerrePositivity.KST.SConstruction
