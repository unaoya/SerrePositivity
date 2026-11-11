module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGActionExactnessReduction
public import SerrePositivity.KST.SConstruction.DGStandardClosedComparisonIso

/-! # 元のラベル付き Perf 作用の完全性
概要：厳密 dg 入力による元のラベル付き Perf 作用は零対象と全 cofiber 列を保つ。
方針：全 Hom 閉零比較を標準 coherent 関手同型へ移し、元の評価同値で完全性を反映する。
規約：同じ元の作用と全 Hom を保持する。使われ方：豊穣 Perf の完全関手空間への精密化。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] (D E : Type v)
  [DGCategory A D] [Small.{u} D] [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

/-- 元の実延長とラベル作用の全 Hom 閉零比較が与える、標準 coherent 関手の実同型。 -/
def presentedPerfectDGStandardActionComparisonIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (dgStandardCoherentMap
      ((presentedPerfectDGEvaluation A D).comp (perfectDGExtension A D E F)))
      (dgStandardCoherentMap
        ((presentedPerfectDGAction A D E F).comp (presentedPerfectDGEvaluation A E))) :=
  dgStandardClosedComparisonIso _ _ (presentedPerfectDGActionIso A D E F)
    (presentedPerfectDGAction_naturality A D E F)

/-- 元のラベル付き Perf の native 作用は、全ての零対象と cofiber 列を保つ。 -/
lemma presentedPerfectDGActionNerve_isExactFunctor :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (presentedPerfectDGAction A D E F)) := by
  apply (presentedPerfectDGAction_isExactFunctor_iff_standardEvaluation A D E F).mpr
  have := presentedPerfectDGStandardExtensionAfterEvaluation_isExactFunctor A D E F
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_functorIso (presentedPerfectDGStandardActionComparisonIso A D E F)

/-- 同じ元のラベル作用を、安定な K 入力間の完全射として使う。 -/
def presentedPerfectDGActionStableMap :
    presentedPerfectDGStableModel A D ⟶ presentedPerfectDGStableModel A E :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (presentedPerfectDGAction A D E F),
    @preservesCofiberData_of_isExactFunctor _ _ _
      (presentedPerfectDGActionNerve_isExactFunctor A D E F)⟩

end SerrePositivity.KST.SConstruction
