module
public import SerrePositivity.InfinityCategories.Stable.LoopSuspensionDiagramsOfEquivalence

/-!
概要：元の loop 四角形の押し出し性と、全 suspension/loop 図式の比較。
方針：同じ指定点の始対象性を実固定 span へ戻し、全図式の評価を比較する。
規約：安定性は仮定しない。使われ方：HA 1.4.2.27 の一般安定性判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 同じ実四角形と全単体の図式を保つ普遍性の比較。 -/
def suspensionLoopSectionOfLoopEquivalence {X : SSet.{u}} [Quasicategory X]
    [HasZeroVertex X] [HasFiniteLimits X] (s : X ⟶ loopDiagrams X)
    (hs : s ≫ loopDiagramEvaluation X 1 1 = 𝟙 X)
    (hΩ : IsQCatEquivalence (s ≫ loopDiagramEvaluation X 0 0)) : X ⟶ loopDiagrams X :=
  suspensionDiagramSectionOfLoopEquivalence s hs hΩ ≫
    (suspensionLoopDiagramsIsoOfLoopEquivalence s hs hΩ).hom

/-- 同じ実四角形と全単体の図式を保つ普遍性の比較。 -/
lemma suspensionLoopSectionOfLoopEquivalence_source {X : SSet.{u}}
    [Quasicategory X] [HasZeroVertex X] [HasFiniteLimits X] (s : X ⟶ loopDiagrams X)
    (hs : s ≫ loopDiagramEvaluation X 1 1 = 𝟙 X)
    (hΩ : IsQCatEquivalence (s ≫ loopDiagramEvaluation X 0 0)) :
    suspensionLoopSectionOfLoopEquivalence s hs hΩ ≫ loopDiagramEvaluation X 0 0 = 𝟙 X := by
  dsimp only [suspensionLoopSectionOfLoopEquivalence]
  rw [Category.assoc, suspensionLoopDiagramsIsoOfLoopEquivalence_evaluation,
    suspensionDiagramSectionOfLoopEquivalence_source]

/-- 同じ実四角形と全単体の図式を保つ普遍性の比較。 -/
lemma suspensionLoopSectionOfLoopEquivalence_target {X : SSet.{u}}
    [Quasicategory X] [HasZeroVertex X] [HasFiniteLimits X] (s : X ⟶ loopDiagrams X)
    (hs : s ≫ loopDiagramEvaluation X 1 1 = 𝟙 X)
    (hΩ : IsQCatEquivalence (s ≫ loopDiagramEvaluation X 0 0)) :
    suspensionLoopSectionOfLoopEquivalence s hs hΩ ≫ loopDiagramEvaluation X 1 1 =
      suspensionFunctorOfLoopEquivalence s hs hΩ := by
  dsimp only [suspensionLoopSectionOfLoopEquivalence, suspensionFunctorOfLoopEquivalence]
  rw [Category.assoc, suspensionLoopDiagramsIsoOfLoopEquivalence_evaluation]

end SerrePositivity.InfinityCategories
