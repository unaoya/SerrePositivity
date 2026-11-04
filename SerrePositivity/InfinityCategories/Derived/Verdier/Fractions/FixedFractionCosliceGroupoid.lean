module
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.FixedFractionCosliceComparison
public import SerrePositivity.KST.LocalizingInvariants.GroupoidCompletionEvaluation

/-! # 同じ全 coslice 評価の亜群化と、既存の商写像空間比較との一致 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
attribute [local instance] vertexFiber_kanComplex_of_leftFibration
variable {X Q : SSet.{u}} [Quasicategory Q] (F : X ⟶ Q)
  (W : Set (X _⦋1⦌)) (hF : InvertsEdges F W) (x y : X _⦋0⦌)

/-- 元の同じ coslice 評価を、元の固定分数の亜群化からの実写像として保持する。 -/
def fixedFractionCosliceGroupoidComparison : groupoidCompletion (fixedMarkedSpans X W x y) ⟶
    vertexFiber (sliceUnderProjection (yonedaEquiv.symm (F.app (Opposite.op ⦋0⦌) x)))
      (F.app (Opposite.op ⦋0⦌) y) :=
  groupoidCompletionEvaluation (fixedFractionCosliceEvaluation F W hF x y)

/-- 同じ亜群化後の coslice 比較は、区間模型へ移すと既存の分数比較そのものに自然同型。 -/
def fixedFractionCosliceGroupoidComparisonIso :
    FunctorIso
      (fixedFractionCosliceGroupoidComparison F W hF x y ≫
        cosliceFiberToIntervalMappingSpace (F.app (Opposite.op ⦋0⦌) x)
          (F.app (Opposite.op ⦋0⦌) y)) (fractionMappingComparison F W hF x y) := by
  apply localizationFactorizationIso _ _ (groupoidCompletion_isLocalization _)
  have e := FunctorIso.postcomp
    (groupoidCompletionEvaluationIso (fixedFractionCosliceEvaluation F W hF x y))
    (cosliceFiberToIntervalMappingSpace (F.app (Opposite.op ⦋0⦌) x)
      (F.app (Opposite.op ⦋0⦌) y)) ≪≫ fixedFractionCosliceComparisonIso F W hF x y ≪≫
        (fractionMappingComparisonIso F W hF x y).symm
  simpa only [Category.assoc, fixedFractionCosliceGroupoidComparison] using e

/-- 同値性を仮定して結論せず、元の全 coslice 評価と既存の分数比較の同じ未完条件を同定する。 -/
theorem fixedFractionCosliceGroupoidComparison_isQCatEquivalence_iff :
    IsQCatEquivalence (fixedFractionCosliceGroupoidComparison F W hF x y) ↔
      IsQCatEquivalence (fractionMappingComparison F W hF x y) := by
  have hc := cosliceFiberToIntervalMappingSpace_isQCatEquivalence
    (F.app (Opposite.op ⦋0⦌) x) (F.app (Opposite.op ⦋0⦌) y)
  have e := fixedFractionCosliceGroupoidComparisonIso F W hF x y
  constructor
  · intro h
    exact (h.comp hc).ofFunctorIso e
  · intro h
    exact hc.cancel_right (h.ofFunctorIso e.symm)

end SerrePositivity.KST.Fibration
