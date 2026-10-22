module
public import SerrePositivity.InfinityCategories.Stable.LoopSectionEvaluation
public import SerrePositivity.InfinityCategories.Core.FixedDiagramVertexEquiv
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
namespace SerrePositivity.InfinityCategories
lemma loopDiagramVertex_evaluation {X : SSet.{u}} (v : (loopDiagrams X) _⦋0⦌)
    (i j : Fin 2) :
    (loopDiagramEvaluation X i j).app (Opposite.op ⦋0⦌) v =
      squareVertex (squareDiagram v.val) i j := by
  have h : functorVertex (squareDiagram v.val) = v.val :=
    (functorVertexEquiv _ _).apply_symm_apply _
  change (evaluateFunctorAt
    (stdSimplex.obj₀Equiv.symm i, stdSimplex.obj₀Equiv.symm j)).app (Opposite.op ⦋0⦌) v.val = _
  rw [← h, evaluateFunctorAt_functorVertex, squareDiagram_functorVertex]
  rfl
def loopSquareOfDiagramVertex {X : SSet.{u}} (v : (loopDiagrams X) _⦋0⦌) :
    LoopSquare ((loopDiagramEvaluation X 1 1).app (Opposite.op ⦋0⦌) v) where
  square := squareDiagram v.val
  zero_corner := (fullSubcomplexOnVertices_vertex v).1
  target_eq := (loopDiagramVertex_evaluation v 1 1).symm
  other_zero := (fullSubcomplexOnVertices_vertex v).2.1
  isPullback := (fullSubcomplexOnVertices_vertex v).2.2
lemma loopSquareOfDiagramVertex_source {X : SSet.{u}} (v : (loopDiagrams X) _⦋0⦌) :
    (loopSquareOfDiagramVertex v).vertex =
      (loopDiagramEvaluation X 0 0).app (Opposite.op ⦋0⦌) v :=
  (loopDiagramVertex_evaluation v 0 0).symm
lemma loopSquareOfDiagramVertex_diagramVertex {X : SSet.{u}}
    (v : (loopDiagrams X) _⦋0⦌) : (loopSquareOfDiagramVertex v).diagramVertex = v := by
  apply Subtype.ext
  exact (functorVertexEquiv _ _).apply_symm_apply v.val
lemma exists_loopSquare_source_iso_of_loopEquivalence {X : SSet.{u}}
    [Quasicategory X] [HasZeroVertex X] (s : X ⟶ loopDiagrams X)
    (hs : s ≫ loopDiagramEvaluation X 1 1 = 𝟙 X)
    (hΩ : IsQCatEquivalence (s ≫ loopDiagramEvaluation X 0 0)) (x : X _⦋0⦌) :
    ∃ (y : X _⦋0⦌) (t : LoopSquare y), Nonempty (VertexIso t.vertex x) := by
  let e := loopDiagramEvaluation_source_isQCatEquivalence_of_loopEquivalence s hs hΩ
  obtain ⟨v, ⟨hv⟩⟩ := e.choose.isEssentiallySurjective x
  refine ⟨_, loopSquareOfDiagramVertex v, ?_⟩
  rw [loopSquareOfDiagramVertex_source]
  exact ⟨hv⟩
def loopDiagramSourceFamilyIso {A X : SSet.{u}}
    [Quasicategory X] [HasZeroVertex X] (s : X ⟶ loopDiagrams X)
    (hs : s ≫ loopDiagramEvaluation X 1 1 = 𝟙 X)
    (hΩ : IsQCatEquivalence (s ≫ loopDiagramEvaluation X 0 0))
    (f g : A ⟶ loopDiagrams X)
    (h : f ≫ loopDiagramEvaluation X 0 0 = g ≫ loopDiagramEvaluation X 0 0) :
    FunctorIso f g := by
  let e := (loopDiagramEvaluation_source_isQCatEquivalence_of_loopEquivalence s hs hΩ).choose
  have hi : f ≫ e.hom ≫ e.inv = g ≫ e.hom ≫ e.inv := by
    change (f ≫ loopDiagramEvaluation X 0 0) ≫ e.inv =
      (g ≫ loopDiagramEvaluation X 0 0) ≫ e.inv
    rw [h]
  exact (FunctorIso.precomp e.homInvIso f).symm ≪≫
    eqToIso (congrArg (fun k ↦ SSet.HomotopyCategory.mk (functorVertex k)) hi) ≪≫
      FunctorIso.precomp e.homInvIso g
end SerrePositivity.InfinityCategories
