module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGComparison
public import SerrePositivity.KST.SConstruction.ExactnessEquivalenceReflection

/-! # 実 Perf 評価の完全性と反映
概要：ラベル評価の native nerve は完全で、その後合成は完全性を反映する。
方針：全 Hom を保持する既存の評価準同値から、実 ∞ 圏同値の判定を適用する。
規約：ラベル付き Perf の対象に Small を仮定しない。使われ方：元の作用の完全性の判定。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 元の評価同値の順方向は、同じ全 Hom 恒等の dg 評価の native nerve。 -/
lemma presentedPerfectDGNerveEquivalence_hom :
    (presentedPerfectDGNerveEquivalence A D).hom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (presentedPerfectDGEvaluation A D) := rfl

/-- 全 Hom 恒等の実 Perf 評価は、零頂点と全 cofiber 列を保存する。 -/
lemma presentedPerfectDGEvaluationNerve_isExactFunctor :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (presentedPerfectDGEvaluation A D)) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_isQCatEquivalence
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerve_map_isQCatEquivalence_of_quasiEquivalence
      (presentedPerfectDGEvaluation A D) (presentedPerfectDGEvaluation_quasiEquivalence A D))

/-- ラベル付き Perf への射の完全性は、同じ実評価の後合成で判定できる。 -/
lemma presentedPerfectDGEvaluationNerve_comp_isExactFunctor_iff
    {X : SSet.{max (u + 1) v}} [Quasicategory X]
    (F : X ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (PresentedPerfectDGObject A D)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (presentedPerfectDGEvaluation A D)) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor F :=
  isExactFunctor_comp_equivalence_iff F (presentedPerfectDGNerveEquivalence A D)

/-- 同じ実評価は、元の安定入力の完全射として使用できる。 -/
def presentedPerfectDGEvaluationStableMap :
    presentedPerfectDGStableModel A D ⟶ perfectDGStableModel A D Set.univ := by
  let h : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (presentedPerfectDGEvaluation A D)) :=
    presentedPerfectDGEvaluationNerve_isExactFunctor A D
  exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (presentedPerfectDGEvaluation A D),
    @preservesCofiberData_of_isExactFunctor _ _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (presentedPerfectDGEvaluation A D)) h⟩

end SerrePositivity.KST.SConstruction
