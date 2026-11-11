module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGEvaluationExact
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGAction
public import SerrePositivity.KST.SConstruction.PerfectDGExtensionExact
public import SerrePositivity.KST.SConstruction.DGStandardExactness

/-! # Perf 作用の完全性を標準 DK 比較へ帰着
概要：元の評価と実延長の合成は完全で、ラベル作用の完全性は比較先で判定できる。
方針：同じ実 dg 関手の合成を保持し、評価同値と標準 DK 比較で完全性を反映する。
規約：比較自然同型はこのファイルでは構成しない。使われ方：全 Hom 閉零比較の移送。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] (D E : Type v)
  [DGCategory A D] [Small.{u} D] [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

/-- 元の評価の後に同じ実 Perf 延長を行う native 関手は完全。 -/
lemma presentedPerfectDGExtensionAfterEvaluation_isExactFunctor :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
      ((presentedPerfectDGEvaluation A D).comp (perfectDGExtension A D E F))) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp]
  have := presentedPerfectDGEvaluationNerve_isExactFunctor A D
  have := perfectDGExtensionNerve_isExactFunctor A D E F
  infer_instance

/-- 元の評価と実延長の合成は、同じ標準 DK coherent nerve 上でも完全。 -/
lemma presentedPerfectDGStandardExtensionAfterEvaluation_isExactFunctor :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (dgStandardCoherentMap
      ((presentedPerfectDGEvaluation A D).comp (perfectDGExtension A D E F))) :=
  (dgNerve_map_isExactFunctor_iff_standard _).mp
    (presentedPerfectDGExtensionAfterEvaluation_isExactFunctor A D E F)

/-- 元のラベル作用の完全性は、評価後の同じ標準 DK 関手の完全性と同値。 -/
lemma presentedPerfectDGAction_isExactFunctor_iff_standardEvaluation :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (presentedPerfectDGAction A D E F)) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (dgStandardCoherentMap
        ((presentedPerfectDGAction A D E F).comp (presentedPerfectDGEvaluation A E))) := by
  have h := (presentedPerfectDGEvaluationNerve_comp_isExactFunctor_iff A E
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (presentedPerfectDGAction A D E F))).symm
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp] at h
  exact h.trans (dgNerve_map_isExactFunctor_iff_standard _)

end SerrePositivity.KST.SConstruction
