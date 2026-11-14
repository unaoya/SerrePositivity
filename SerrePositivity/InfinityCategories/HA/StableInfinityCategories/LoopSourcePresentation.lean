module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LoopSectionEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FixedDiagramVertexEquiv
/-!
概要：始点評価の同値性から実 loop 四角形とその全図式比較を回収する。
方針：全頂点の厳密な復元・二評価の式と本質的全射性を使う。
規約：押し出し性を先取りしない。使われ方：HA 1.4.2.27 の普遍余錐比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
lemma loopDiagramVertex_evaluation {X : SSet.{u}} (v : (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams X) _⦋0⦌)
    (i j : Fin 2) :
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X i j).app (Opposite.op ⦋0⦌) v =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram v.val) i j := by
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram v.val) = v.val :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).apply_symm_apply _
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
    (stdSimplex.obj₀Equiv.symm i, stdSimplex.obj₀Equiv.symm j)).app (Opposite.op ⦋0⦌) v.val = _
  rw [← h, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagram_functorVertex]
  rfl
def loopSquareOfDiagramVertex {X : SSet.{u}} (v : (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams X) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LoopSquare ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 1 1).app (Opposite.op ⦋0⦌) v) where
  square := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram v.val
  zero_corner := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex v).1
  target_eq := (loopDiagramVertex_evaluation v 1 1).symm
  other_zero := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex v).2.1
  isPullback := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex v).2.2
lemma loopSquareOfDiagramVertex_source {X : SSet.{u}} (v : (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams X) _⦋0⦌) :
    (loopSquareOfDiagramVertex v).vertex =
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 0 0).app (Opposite.op ⦋0⦌) v :=
  (loopDiagramVertex_evaluation v 0 0).symm
lemma loopSquareOfDiagramVertex_diagramVertex {X : SSet.{u}}
    (v : (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams X) _⦋0⦌) : (loopSquareOfDiagramVertex v).diagramVertex = v := by
  apply Subtype.ext
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).apply_symm_apply v.val
lemma exists_loopSquare_source_iso_of_loopEquivalence {X : SSet.{u}}
    [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex X] (s : X ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams X)
    (hs : s ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 1 1 = 𝟙 X)
    (hΩ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (s ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 0 0)) (x : X _⦋0⦌) :
    ∃ (y : X _⦋0⦌) (t : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LoopSquare y), Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso t.vertex x) := by
  let e := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation_source_isQCatEquivalence_of_loopEquivalence s hs hΩ
  obtain ⟨v, ⟨hv⟩⟩ := e.choose.isEssentiallySurjective x
  refine ⟨_, loopSquareOfDiagramVertex v, ?_⟩
  rw [loopSquareOfDiagramVertex_source]
  exact ⟨hv⟩
def loopDiagramSourceFamilyIso {A X : SSet.{u}}
    [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex X] (s : X ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams X)
    (hs : s ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 1 1 = 𝟙 X)
    (hΩ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (s ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 0 0))
    (f g : A ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams X)
    (h : f ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 0 0 = g ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 0 0) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g := by
  let e := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation_source_isQCatEquivalence_of_loopEquivalence s hs hΩ).choose
  have hi : f ≫ e.hom ≫ e.inv = g ≫ e.hom ≫ e.inv := by
    change (f ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 0 0) ≫ e.inv =
      (g ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 0 0) ≫ e.inv
    rw [h]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp e.homInvIso f).symm ≪≫
    eqToIso (congrArg (fun k ↦ SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex k)) hi) ≪≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp e.homInvIso g
end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
