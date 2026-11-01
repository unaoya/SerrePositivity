module
public import SerrePositivity.InfinityCategories.Stable.SuspensionLoopInverseOfEquivalence
public import SerrePositivity.InfinityCategories.F1B.QCatEquivalenceAdjunction
/-!
概要：実 suspension と元の loop 関手の自己同値および三角式付き随伴。
方針：全関手として構成した両逆性を同値の随伴化へ送る。
規約：安定性は仮定しない。使われ方：一般安定性判定の Σ・Ω 比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 元の実 Σ と Ω を同じ全関手として保持する。 -/
def suspensionLoopEquivalenceOfLoopEquivalence {X : SSet.{u}} [Quasicategory X]
    [HasZeroVertex X] [HasFiniteLimits X] (s : X ⟶ loopDiagrams X)
    (hs : s ≫ loopDiagramEvaluation X 1 1 = 𝟙 X)
    (hΩ : IsQCatEquivalence (s ≫ loopDiagramEvaluation X 0 0)) : QCatEquivalence X X where
  hom := suspensionFunctorOfLoopEquivalence s hs hΩ
  inv := s ≫ loopDiagramEvaluation X 0 0
  homInvIso := suspensionLoopInverseIsoOfLoopEquivalence s hs hΩ
  invHomIso := loopSuspensionInverseIsoOfLoopEquivalence s hs hΩ

/-- 元の実 Σ と Ω を同じ全関手として保持する。 -/
def suspensionLoopAdjunctionOfLoopEquivalence {X : SSet.{u}} [Quasicategory X]
    [HasZeroVertex X] [HasFiniteLimits X] (s : X ⟶ loopDiagrams X)
    (hs : s ≫ loopDiagramEvaluation X 1 1 = 𝟙 X)
    (hΩ : IsQCatEquivalence (s ≫ loopDiagramEvaluation X 0 0)) :
    QCatAdjunction (suspensionFunctorOfLoopEquivalence s hs hΩ)
      (s ≫ loopDiagramEvaluation X 0 0) :=
  (suspensionLoopEquivalenceOfLoopEquivalence s hs hΩ).toAdjunction
end SerrePositivity.InfinityCategories
