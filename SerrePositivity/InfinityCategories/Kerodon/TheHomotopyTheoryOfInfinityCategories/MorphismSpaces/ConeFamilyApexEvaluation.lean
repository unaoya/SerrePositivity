module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.ConeFamilyApex
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.ConeRestrictionCocartesianEdge
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomEvaluationNaturality

/-!
概要：固定図式上の全錐の頂点射影は、同じ全錐の関手の頂点評価と一致する。
方針：既存の一点関手評価と前合成の可換式を使う。
規約：Kerodon Example 4.6.6.8（Tag 04J5）、HTT §1.2.13の既存評価の計算法則。
使われ方：S8 の右Kan輸送の頂点射を、元の標準極限比較へ戻す。
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 元の同じ錐のfiberの射影は、全錐の関手の頂点評価に厳密に一致する。 -/
lemma coneFamilyApex_eq_evaluation {K X : SSet.{u}} (p : K ⟶ X) :
    coneFamilyApex p = vertexFiberι (coneRestriction K X)
      (SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p) ≫
        coneApexEvaluation K X := by
  rw [coneFamilyApex, pointFunctorEvaluationIso,
    evaluateFunctorAt_precomp]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
