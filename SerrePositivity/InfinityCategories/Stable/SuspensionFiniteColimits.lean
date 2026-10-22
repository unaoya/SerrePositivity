module
public import SerrePositivity.InfinityCategories.Stable.Definition
public import SerrePositivity.InfinityCategories.Stable.LoopSuspensionSquareExists
public import SerrePositivity.InfinityCategories.Stable.SuspensionEvaluationFromSquares

/-!
概要：有限余極限から suspension 図式の実厳密切断と同じ全関手を構成する。
方針：同じ実図式の貼り合わせ・全パラメーターの評価・普遍的な切断比較を使う。
規約：一般安定性を先取りしない。使われ方：HA 1.4.2.15 の実 θ の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

lemma suspensionSquare_nonempty_of_finiteColimits {X : SSet.{u}} [Quasicategory X]
    [HasZeroVertex X] [HasFiniteColimits X] (x : X _⦋0⦌) : Nonempty (SuspensionSquare x) := by
  obtain ⟨b⟩ := (zeroOuterSpanSourceFiber_isContractibleKan X x).nonempty
  let d := b.val
  let p := (functorVertexEquiv _ X).symm d.val
  have hp : functorVertex p = d.val := (functorVertexEquiv _ X).apply_symm_apply d.val
  obtain ⟨c, hc⟩ := HasFiniteColimits.hasColimit p
  let F := coconeSquare c
  have hP : IsZeroCornerSquareVertex (functorVertex F) := by
    apply (zeroOuterSpanVertex_square_iff (functorVertex F)).mp
    change IsZeroOuterSpanVertex (functorVertex (pushoutSpan F))
    rw [coconeSquare_span, hp]
    exact fullSubcomplexOnVertices_vertex d
  have hz : IsZeroVertex (squareVertex F 1 0) ∧ IsZeroVertex (squareVertex F 0 1) := by
    simpa only [IsZeroCornerSquareVertex, squareDiagram_functorVertex] using hP
  let w : (zeroCornerSquares X) _⦋0⦌ := ⟨functorVertex F, by
    intro α
    have hα : α = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
    rw [hα, op_id, CategoryTheory.Functor.map_id_apply]
    exact hP⟩
  have hwd : (zeroCornerSquareSpan X).app (Opposite.op ⦋0⦌) w = d := by
    apply Subtype.ext
    change functorVertex (pushoutSpan F) = d.val
    rw [coconeSquare_span, hp]
  have hsource : squareVertex F 0 0 = x := by
    calc
      _ = (zeroCornerSquareSource X).app (Opposite.op ⦋0⦌) w :=
        (evaluateFunctorAt_functorVertex _ F).symm
      _ = (zeroOuterSpanSource X).app (Opposite.op ⦋0⦌)
          ((zeroCornerSquareSpan X).app (Opposite.op ⦋0⦌) w) := by
        exact (ConcreteCategory.congr_hom
          (NatTrans.congr_app (zeroCornerSquareSpan_source X) (Opposite.op ⦋0⦌)) w).symm
      _ = (zeroOuterSpanSource X).app (Opposite.op ⦋0⦌) d := by rw [hwd]
      _ = x := b.property.trans (pinchedConstant_zero x)
  exact ⟨{
    square := F
    zero_corner := hz.2
    other_zero := hz.1
    source_eq := hsource
    isPushout := coconeSquare_isPushout c hc }⟩

lemma suspensionDiagramEvaluation_source_trivialKanFibration_of_finiteColimits
    (X : SSet.{u}) [Quasicategory X] [HasZeroVertex X] [HasFiniteColimits X] :
    TrivialKanFibration (suspensionDiagramEvaluation X 0 0) :=
  suspensionDiagramEvaluation_source_trivialKanFibration_of_squares X
    suspensionSquare_nonempty_of_finiteColimits

def suspensionDiagramSectionOfFiniteColimits (X : SSet.{u}) [Quasicategory X]
    [HasZeroVertex X] [HasFiniteColimits X] : X ⟶ suspensionDiagrams X :=
  let := suspensionDiagramEvaluation_source_trivialKanFibration_of_finiteColimits X
  Classical.choose (trivialKanFibration_exists_section (suspensionDiagramEvaluation X 0 0))

lemma suspensionDiagramSectionOfFiniteColimits_source (X : SSet.{u}) [Quasicategory X]
    [HasZeroVertex X] [HasFiniteColimits X] :
    suspensionDiagramSectionOfFiniteColimits X ≫ suspensionDiagramEvaluation X 0 0 = 𝟙 X := by
  let := suspensionDiagramEvaluation_source_trivialKanFibration_of_finiteColimits X
  exact Classical.choose_spec
    (trivialKanFibration_exists_section (suspensionDiagramEvaluation X 0 0))

def suspensionFunctorOfFiniteColimits (X : SSet.{u}) [Quasicategory X]
    [HasZeroVertex X] [HasFiniteColimits X] : X ⟶ X :=
  suspensionDiagramSectionOfFiniteColimits X ≫ suspensionDiagramEvaluation X 1 1

end SerrePositivity.InfinityCategories
