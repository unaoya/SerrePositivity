module
public import SerrePositivity.InfinityCategories.Stable.SuspensionEvaluationFromSquares
public import SerrePositivity.InfinityCategories.Stable.LoopSuspensionSquareExists

/-!
概要：固定 span の余錐比較から suspension の普遍四角形と厳密切断を構成する。
方針：実 fiber の同型で始対象性を余極限性へ戻し、全境界持ち上げを使う。
規約：安定性・有限余極限は仮定しない。使われ方：一般安定性判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 同じ固定 span の普遍性と suspension の全単体構成。 -/
lemma suspensionDiagramEvaluation_source_trivialKanFibration_of_loopEquivalence
    {X : SSet.{u}} [Quasicategory X] [HasZeroVertex X] [HasFiniteLimits X]
    (s : X ⟶ loopDiagrams X) (hs : s ≫ loopDiagramEvaluation X 1 1 = 𝟙 X)
    (hΩ : IsQCatEquivalence (s ≫ loopDiagramEvaluation X 0 0)) :
    TrivialKanFibration (suspensionDiagramEvaluation X 0 0) :=
  suspensionDiagramEvaluation_source_trivialKanFibration_of_squares X
    (suspensionSquare_nonempty_of_loopEquivalence s hs hΩ)

/-- 同じ固定 span の普遍性と suspension の全単体構成。 -/
def suspensionDiagramSectionOfLoopEquivalence {X : SSet.{u}} [Quasicategory X]
    [HasZeroVertex X] [HasFiniteLimits X]
    (s : X ⟶ loopDiagrams X) (hs : s ≫ loopDiagramEvaluation X 1 1 = 𝟙 X)
    (hΩ : IsQCatEquivalence (s ≫ loopDiagramEvaluation X 0 0)) : X ⟶ suspensionDiagrams X :=
  let := suspensionDiagramEvaluation_source_trivialKanFibration_of_loopEquivalence s hs hΩ
  Classical.choose (trivialKanFibration_exists_section (suspensionDiagramEvaluation X 0 0))

/-- 同じ固定 span の普遍性と suspension の全単体構成。 -/
lemma suspensionDiagramSectionOfLoopEquivalence_source {X : SSet.{u}} [Quasicategory X]
    [HasZeroVertex X] [HasFiniteLimits X]
    (s : X ⟶ loopDiagrams X) (hs : s ≫ loopDiagramEvaluation X 1 1 = 𝟙 X)
    (hΩ : IsQCatEquivalence (s ≫ loopDiagramEvaluation X 0 0)) :
    suspensionDiagramSectionOfLoopEquivalence s hs hΩ ≫
      suspensionDiagramEvaluation X 0 0 = 𝟙 X := by
  let := suspensionDiagramEvaluation_source_trivialKanFibration_of_loopEquivalence s hs hΩ
  exact Classical.choose_spec
    (trivialKanFibration_exists_section (suspensionDiagramEvaluation X 0 0))


/-- 同じ固定 span の普遍性と suspension の全単体構成。 -/
lemma suspensionDiagramSectionOfLoopEquivalence_isQCatEquivalence
    {X : SSet.{u}} [Quasicategory X] [HasZeroVertex X] [HasFiniteLimits X]
    (s : X ⟶ loopDiagrams X) (hs : s ≫ loopDiagramEvaluation X 1 1 = 𝟙 X)
    (hΩ : IsQCatEquivalence (s ≫ loopDiagramEvaluation X 0 0)) :
    IsQCatEquivalence (suspensionDiagramSectionOfLoopEquivalence s hs hΩ) := by
  have := suspensionDiagramEvaluation_source_trivialKanFibration_of_loopEquivalence s hs hΩ
  apply (isQCatEquivalence_of_trivialKanFibration (suspensionDiagramEvaluation X 0 0)).cancel_right
  rw [suspensionDiagramSectionOfLoopEquivalence_source]
  exact (QCatEquivalence.refl X).isQCatEquivalence

/-- 同じ固定 span の普遍性と suspension の全単体構成。 -/
def suspensionFunctorOfLoopEquivalence {X : SSet.{u}} [Quasicategory X]
    [HasZeroVertex X] [HasFiniteLimits X]
    (s : X ⟶ loopDiagrams X) (hs : s ≫ loopDiagramEvaluation X 1 1 = 𝟙 X)
    (hΩ : IsQCatEquivalence (s ≫ loopDiagramEvaluation X 0 0)) : X ⟶ X :=
  suspensionDiagramSectionOfLoopEquivalence s hs hΩ ≫ suspensionDiagramEvaluation X 1 1
end SerrePositivity.InfinityCategories
