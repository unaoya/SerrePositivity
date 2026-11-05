module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.FixedFractionCosliceComparison
public import SerrePositivity.InfinityCategories.Derived.Localization.GroupoidCompletionEvaluation

/-! # 同じ全 coslice 評価の亜群化と、既存の商写像空間比較との一致 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
end SerrePositivity.KST.Fibration
namespace SerrePositivity.InfinityCategories.Derived.Verdier.Fractions
open SerrePositivity.KST.Fibration
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

end SerrePositivity.InfinityCategories.Derived.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionCosliceGroupoidComparison (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.fixedFractionCosliceGroupoidComparison := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionCosliceGroupoidComparison

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionCosliceGroupoidComparisonIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.fixedFractionCosliceGroupoidComparisonIso := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionCosliceGroupoidComparisonIso

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.fixedFractionCosliceGroupoidComparison_isQCatEquivalence_iff := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionCosliceGroupoidComparison_isQCatEquivalence_iff

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.fixedFractionCosliceGroupoidComparison._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionCosliceGroupoidComparison._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.fixedFractionCosliceGroupoidComparison.eq_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionCosliceGroupoidComparison.eq_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.fixedFractionCosliceGroupoidComparisonIso._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionCosliceGroupoidComparisonIso._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.fixedFractionCosliceGroupoidComparisonIso._proof_2 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionCosliceGroupoidComparisonIso._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.fixedFractionCosliceGroupoidComparisonIso._proof_3 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionCosliceGroupoidComparisonIso._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.fixedFractionCosliceGroupoidComparisonIso._proof_4 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionCosliceGroupoidComparisonIso._proof_4
