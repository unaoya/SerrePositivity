module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorLaxInputComparison

/-!
概要：元の角代数の実 Perf 値を、同じ固定 ν 角へ照合する。
方針：同じ対象宇宙下降の一回 Perf 延長と元 presented Perf 評価を合成する。
規約：元の角代数を保持し、全 Perf の Small 性は仮定しない。
使われ方：元二脚の実 cone と lax cofiber 差の全比較の終域を指定する。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet DifferentialGraded InfinityCategories LocalizingInvariants
variable (R : Type u) [CommRing R] (d : DGOdotInput R)

/-- 概要：同じ角入力の対象宇宙下降は実 Perf 同値を誘導する。
方針：元の準同値の一回 Perf 延長を使う。規約：角を選び直さない。
使われ方：元 Perf 角と固定 ν 角の比較の中間。 -/
def dgOdotMilnorCornerPerfectDownEquivalence : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (PerfectDGModule R (dgOdotCornerInput R d)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (PerfectDGModule R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.corner))) := by
  let F := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, 0, u + 1} R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.corner)
  letI : (quasiEquivalencePerfectExtension R
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{0, u + 1} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.corner))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.corner) F).IsEquivalence :=
    (quasiEquivalencePerfectEquivalence R _ _ F
      (dgKUniverseLiftDown_quasiEquivalence R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.corner))).isEquivalence_functor
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerve_map_isQCatEquivalence_of_quasiEquivalence
    (perfectDGExtension R _ _ F) (perfectDGExtension_quasiEquivalence R _ _ F)).choose

/-- 概要：元角代数の実 Perf nerve と同じ固定 ν 角値の指定同値。
方針：対象宇宙下降と元 presented Perf 評価の逆を合成する。
規約：元の実評価を保持。使われ方：D2 に依頼する全 cone 比較の終域指定。 -/
def dgOdotMilnorCornerPerfectValueEquivalence : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (PerfectDGModule R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.corner)))
    (dgKInputStableValue R (dgOdotCornerInput R d)).obj :=
  (dgOdotMilnorCornerPerfectDownEquivalence R d).symm.trans
    (presentedPerfectDGQCatEvaluationEquivalence R (dgOdotCornerInput R d)).symm
end SerrePositivity.KST.SConstruction
