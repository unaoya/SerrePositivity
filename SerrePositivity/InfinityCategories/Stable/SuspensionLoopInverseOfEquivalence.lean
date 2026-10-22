module
public import SerrePositivity.InfinityCategories.Stable.SuspensionLoopSectionOfEquivalence

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
def suspensionLoopInverseIsoOfLoopEquivalence {X : SSet.{u}} [Quasicategory X]
    [HasZeroVertex X] [HasFiniteLimits X] (s : X ⟶ loopDiagrams X)
    (hs : s ≫ loopDiagramEvaluation X 1 1 = 𝟙 X)
    (hΩ : IsQCatEquivalence (s ≫ loopDiagramEvaluation X 0 0)) :
    FunctorIso (suspensionFunctorOfLoopEquivalence s hs hΩ ≫
      (s ≫ loopDiagramEvaluation X 0 0)) (𝟙 X) := by
  let b := suspensionLoopSectionOfLoopEquivalence s hs hΩ
  have hb : b ≫ loopDiagramEvaluation X 0 0 = 𝟙 X :=
    suspensionLoopSectionOfLoopEquivalence_source s hs hΩ
  have ht : b ≫ loopDiagramEvaluation X 1 1 =
      suspensionFunctorOfLoopEquivalence s hs hΩ :=
    suspensionLoopSectionOfLoopEquivalence_target s hs hΩ
  let e := loopDiagramFamilyIso_of_section s hs (b ≫ loopDiagramEvaluation X 1 1 ≫ s) b
    (by simp only [Category.assoc, hs, Category.comp_id])
  have h := e.postcomp (loopDiagramEvaluation X 0 0)
  simpa only [← Category.assoc, ht, hb] using h

/-- 同じ実四角形と全単体の図式を保つ普遍性の比較。 -/
def loopSuspensionInverseIsoOfLoopEquivalence {X : SSet.{u}} [Quasicategory X]
    [HasZeroVertex X] [HasFiniteLimits X] (s : X ⟶ loopDiagrams X)
    (hs : s ≫ loopDiagramEvaluation X 1 1 = 𝟙 X)
    (hΩ : IsQCatEquivalence (s ≫ loopDiagramEvaluation X 0 0)) :
    FunctorIso ((s ≫ loopDiagramEvaluation X 0 0) ≫
      suspensionFunctorOfLoopEquivalence s hs hΩ) (𝟙 X) := by
  let b := suspensionLoopSectionOfLoopEquivalence s hs hΩ
  have hb : b ≫ loopDiagramEvaluation X 0 0 = 𝟙 X :=
    suspensionLoopSectionOfLoopEquivalence_source s hs hΩ
  have ht : b ≫ loopDiagramEvaluation X 1 1 =
      suspensionFunctorOfLoopEquivalence s hs hΩ :=
    suspensionLoopSectionOfLoopEquivalence_target s hs hΩ
  let e := loopDiagramSourceFamilyIso s hs hΩ (s ≫ loopDiagramEvaluation X 0 0 ≫ b) s
    (by simp only [Category.assoc, hb, Category.comp_id])
  have h := e.postcomp (loopDiagramEvaluation X 1 1)
  simpa only [Category.assoc, ht, hs] using h

end SerrePositivity.InfinityCategories
