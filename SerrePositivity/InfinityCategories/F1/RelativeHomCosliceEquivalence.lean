module

public import SerrePositivity.InfinityCategories.F1.RelativeHomIdentityAction
public import SerrePositivity.InfinityCategories.F1.LeftFibrationFiberComparison

/-!
概要：実際の Hom 大域比較の各 fiber の同値性を、同じ恒等射の作用から証明する。
方針：恒等係数への合成作用の標準同型と pointed fiber 比較を合成し、標準 Hom 比較を消去する。
規約：構成済みの同じ大域比較の fiber 射を使用する。
使われ方：表現可能 coslice と Hom 関手の unstraightening の大域同値。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 全 Hom の恒等射係数への作用は、実際の反転した一点関手空間への同型。 -/
lemma relativeHomIdentityAction_isIso {B : SSet.{u}} (q r : LeftFibrationObject B) :
    IsIso (relativeHomIdentityAction q r) := by
  rw [relativeHomIdentityAction_eq]
  infer_instance

/-- 元の一つの大域比較の実際の pointed fiber 射は、各対象で同値。 -/
lemma relativeHomCosliceComparisonFiber_isQCatEquivalence {B : SSet.{u}}
    (q r : LeftFibrationObject B) : IsQCatEquivalence (relativeHomCosliceComparisonFiber q r) := by
  have := relativeHomIdentityAction_isIso q r
  have h₀ := (qCatEquivalenceOfIso (asIso (relativeHomIdentityAction q r))).isQCatEquivalence.comp
    (pointedReverseKanFiberComparison_isQCatEquivalence
      ((relativeFunctorEnrichedEvaluation q.val).obj r))
  have h₁ := h₀.ofFunctorIso (relativeHomCosliceComparisonFiber_identityActionIso q r).symm
  have hk := (qCatEquivalenceOfIso
    (HomotopyLimits.uliftOppositeIso (SimplicialCategory.sHom q r)).symm).isQCatEquivalence.comp
      (HomotopyLimits.coherentCosliceFiberComparison_homotopyEquivalence q r).isQCatEquivalence
  exact hk.cancel_left h₁

/-- 元の大域比較の native な fiber 射も、既存の同じ fiber 同型を消去して同値。 -/
lemma relativeHomCosliceComparison_nativeFiber_isQCatEquivalence {B : SSet.{u}}
    (q r : LeftFibrationObject B) :
    IsQCatEquivalence (vertexFiberMap _ _ (relativeHomCosliceComparison q)
      (relativeHomCosliceComparison_projection q) (coherentNerveVertex r)) := by
  exact (qCatEquivalenceOfIso
    (relativeHomUnstraighteningFiberIso q r)).isQCatEquivalence.cancel_right
    (relativeHomCosliceComparisonFiber_isQCatEquivalence q r)

/-- 恒等点から構成した一つの coslice 比較は、全空間の実際の同値。 -/
lemma relativeHomCosliceComparison_isQCatEquivalence {B : SSet.{u}}
    (q : LeftFibrationObject B) : IsQCatEquivalence (relativeHomCosliceComparison q) := by
  apply isQCatEquivalence_of_leftFibration_fibers
    (sliceUnderProjection (SSet.yonedaEquiv.symm (coherentNerveVertex q)))
    (leftUnstraighteningProjection (leftFibrationCoherentEvaluation q.val))
    (relativeHomCosliceComparison q) (relativeHomCosliceComparison_projection q)
  intro s
  obtain ⟨r, rfl⟩ := (coherentNerveVertexEquiv (LeftFibrationObject B)).surjective s
  exact relativeHomCosliceComparison_nativeFiber_isQCatEquivalence q r

end SerrePositivity.InfinityCategories
