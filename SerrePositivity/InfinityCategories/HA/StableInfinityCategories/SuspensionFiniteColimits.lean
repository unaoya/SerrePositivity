module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Definition
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LoopSuspensionSquareExists
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionEvaluationFromSquares

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
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

lemma suspensionSquare_nonempty_of_finiteColimits {X : SSet.{u}} [Quasicategory X]
    [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex X] [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteColimits X] (x : X _⦋0⦌) : Nonempty (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare x) := by
  obtain ⟨b⟩ := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroOuterSpanSourceFiber_isContractibleKan X x).nonempty
  let d := b.val
  let p := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ X).symm d.val
  have hp : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p = d.val := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ X).apply_symm_apply d.val
  obtain ⟨c, hc⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteColimits.hasColimit p
  let F := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coconeSquare c
  have hP : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsZeroCornerSquareVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) := by
    apply (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroOuterSpanVertex_square_iff (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F)).mp
    change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsZeroOuterSpanVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan F))
    rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coconeSquare_span, hp]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex d
  have hz : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex F 1 0) ∧ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex F 0 1) := by
    simpa only [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsZeroCornerSquareVertex, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagram_functorVertex] using hP
  let w : (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroCornerSquares X) _⦋0⦌ := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F, by
    intro α
    have hα : α = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
    rw [hα, op_id, CategoryTheory.Functor.map_id_apply]
    exact hP⟩
  have hwd : (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroCornerSquareSpan X).app (Opposite.op ⦋0⦌) w = d := by
    apply Subtype.ext
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan F) = d.val
    rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coconeSquare_span, hp]
  have hsource : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex F 0 0 = x := by
    calc
      _ = (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroCornerSquareSource X).app (Opposite.op ⦋0⦌) w :=
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex _ F).symm
      _ = (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroOuterSpanSource X).app (Opposite.op ⦋0⦌)
          ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroCornerSquareSpan X).app (Opposite.op ⦋0⦌) w) := by
        exact (ConcreteCategory.congr_hom
          (NatTrans.congr_app (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroCornerSquareSpan_source X) (Opposite.op ⦋0⦌)) w).symm
      _ = (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroOuterSpanSource X).app (Opposite.op ⦋0⦌) d := by rw [hwd]
      _ = x := b.property.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero x)
  exact ⟨{
    square := F
    zero_corner := hz.2
    other_zero := hz.1
    source_eq := hsource
    isPushout := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coconeSquare_isPushout c hc }⟩

lemma suspensionDiagramEvaluation_source_trivialKanFibration_of_finiteColimits
    (X : SSet.{u}) [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex X] [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteColimits X] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.suspensionDiagramEvaluation X 0 0) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionDiagramEvaluation_source_trivialKanFibration_of_squares X
    suspensionSquare_nonempty_of_finiteColimits

def suspensionDiagramSectionOfFiniteColimits (X : SSet.{u}) [Quasicategory X]
    [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex X] [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteColimits X] : X ⟶ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.suspensionDiagrams X :=
  let := suspensionDiagramEvaluation_source_trivialKanFibration_of_finiteColimits X
  Classical.choose (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.trivialKanFibration_exists_section (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.suspensionDiagramEvaluation X 0 0))

lemma suspensionDiagramSectionOfFiniteColimits_source (X : SSet.{u}) [Quasicategory X]
    [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex X] [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteColimits X] :
    suspensionDiagramSectionOfFiniteColimits X ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.suspensionDiagramEvaluation X 0 0 = 𝟙 X := by
  let := suspensionDiagramEvaluation_source_trivialKanFibration_of_finiteColimits X
  exact Classical.choose_spec
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.trivialKanFibration_exists_section (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.suspensionDiagramEvaluation X 0 0))

def suspensionFunctorOfFiniteColimits (X : SSet.{u}) [Quasicategory X]
    [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex X] [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteColimits X] : X ⟶ X :=
  suspensionDiagramSectionOfFiniteColimits X ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.suspensionDiagramEvaluation X 1 1

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
