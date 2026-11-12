module
public import SerrePositivity.KST.SConstruction.DGStandardEquivalence
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGActionExact
public import SerrePositivity.KST.SConstruction.PerfectDGMoritaRealization
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGExactValues

/-! # 元の実ラベル付き Perf 作用の Morita 同値性
概要：元の主 Perf 作用が同値なら、同じラベル付き native Perf 作用も同値。
方針：実評価と実延長の標準 DK 比較同型を使い、評価同値を消去する。
規約：同じ元の作用を保持する。使われ方：厳密豊穣 BF K 射の Morita 不変性。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] (D E : Type v)
  [DGCategory A D] [Small.{u} D] [DGCategory A E] [Small.{u} E]
  (F : DGFunctor A D E) [(quasiEquivalencePerfectExtension A D E F).IsEquivalence]

/-- 元の主 Perf 同値は、同じラベル付き native Perf 作用も同値にする。 -/
lemma presentedPerfectDGMoritaAction_isQCatEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (presentedPerfectDGAction A D E F)) := by
  have hd := (presentedPerfectDGNerveEquivalence A D).isQCatEquivalence
  have he := (presentedPerfectDGNerveEquivalence A E).isQCatEquivalence
  have hp := perfectDGMoritaNerve_isQCatEquivalence A D E F
  have hcomp : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
      ((presentedPerfectDGEvaluation A D).comp (perfectDGExtension A D E F))) := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp]
    exact hd.comp hp
  have hs := (dgNerve_map_isQCatEquivalence_iff_standard _).mp hcomp
  have ht := hs.ofFunctorIso (presentedPerfectDGStandardActionComparisonIso A D E F)
  have hn := (dgNerve_map_isQCatEquivalence_iff_standard _).mpr ht
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp] at hn
  exact he.cancel_right hn

end SerrePositivity.KST.SConstruction
