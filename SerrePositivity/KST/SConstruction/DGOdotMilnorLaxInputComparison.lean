module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorLaxModel
public import SerrePositivity.KST.SConstruction.DGOdotLaxVerdierConnection

/-!
概要：D2 lax 模型の元小 Perf 二因子を、元代数の固定 ν 値へ照合する。
方針：同じ小模型評価・Perf 評価・対象宇宙を下げる実一回延長を合成する。
規約：二脚の基底全体との照合や元の四角形の比較は別に保持する。
使われ方：LT の二因子を元代数の実 Perf 値として回収する。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet DifferentialGraded InfinityCategories LocalizingInvariants
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "A" => _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R (DGOdotInput.source d)
local notation "C" => DGSmallPerfectArrowTarget R (A) (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R d.left)
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.top)
local notation "D" => DGSmallPerfectArrowTarget R (A) (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R d.right)
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.side)

/-- 概要：元左代数の同じ対象宇宙を下げる射の実 Perf 延長同値。
方針：元の準同値と一回 Perf 延長を使う。規約：元代数を選び直さない。
使われ方：固定 ν と元小 Perf 模型の比較の中間。 -/
def dgOdotMilnorLeftPerfectDownEquivalence : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (PerfectDGModule R (dgOdotLeftInput R d)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (PerfectDGModule R (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R d.left))) := by
  let F := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, 0, u + 1} R (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R d.left)
  letI : (quasiEquivalencePerfectExtension R
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{0, u + 1} (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R d.left))
      (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R d.left) F).IsEquivalence :=
    (quasiEquivalencePerfectEquivalence R _ _ F
      (dgKUniverseLiftDown_quasiEquivalence R (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R d.left))).isEquivalence_functor
  exact (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.dgNerve_map_isQCatEquivalence_of_quasiEquivalence
    (perfectDGExtension R _ _ F) (perfectDGExtension_quasiEquivalence R _ _ F)).choose

/-- 概要：元右代数の同じ対象宇宙を下げる射の実 Perf 延長同値。
方針：元の準同値と一回 Perf 延長を使う。規約：元代数を選び直さない。
使われ方：固定 ν と元小 Perf 模型の比較の中間。 -/
def dgOdotMilnorRightPerfectDownEquivalence : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (PerfectDGModule R (dgOdotRightInput R d)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (PerfectDGModule R (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R d.right))) := by
  let F := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, 0, u + 1} R (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R d.right)
  letI : (quasiEquivalencePerfectExtension R
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{0, u + 1} (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R d.right))
      (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R d.right) F).IsEquivalence :=
    (quasiEquivalencePerfectEquivalence R _ _ F
      (dgKUniverseLiftDown_quasiEquivalence R (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R d.right))).isEquivalence_functor
  exact (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.dgNerve_map_isQCatEquivalence_of_quasiEquivalence
    (perfectDGExtension R _ _ F) (perfectDGExtension_quasiEquivalence R _ _ F)).choose

/-- 概要：元左代数の固定 ν 値から同じ実 lax 第一因子への指定同値。
方針：元の実評価・対象宇宙比較・小模型評価の逆を全単体で合成する。
規約：実二脚の比較そのものとは区別する。使われ方：元の左 Perf 値の回収。 -/
def dgOdotMilnorLaxLeftInputEquivalence : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence
    (dgKInputStableValue R (dgOdotLeftInput R d)).obj (dgOdotMilnorLaxLeft R d).obj :=
  (((presentedPerfectDGQCatEvaluationEquivalence R (dgOdotLeftInput R d)).trans
    (dgOdotMilnorLeftPerfectDownEquivalence R d)).trans
    (dgSmallPerfectEnvelopeNerveEquivalence R (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R d.left)
      (DGSmallPerfectBase R (A))
      (dgSmallPerfectEnvelopeExtensionFamily R (A) (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R d.left) Empty
        (dgSmallPerfectBaseFamily R (A)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.top))).symm).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso
      (Functor.isoWhiskerLeft (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (C)) CategoryTheory.uliftFunctorTrivial ≪≫
        Functor.rightUnitor _).symm)

/-- 概要：元右代数の固定 ν 値から同じ実 lax 第二因子への指定同値。
方針：元の実評価・対象宇宙比較・小模型評価の逆を全単体で合成する。
規約：因子の順序を保つ。使われ方：元の右 Perf 値の回収。 -/
def dgOdotMilnorLaxRightInputEquivalence : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence
    (dgKInputStableValue R (dgOdotRightInput R d)).obj (dgOdotMilnorLaxRight R d).obj :=
  (((presentedPerfectDGQCatEvaluationEquivalence R (dgOdotRightInput R d)).trans
    (dgOdotMilnorRightPerfectDownEquivalence R d)).trans
    (dgSmallPerfectEnvelopeNerveEquivalence R (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R d.right)
      (DGSmallPerfectBase R (A))
      (dgSmallPerfectEnvelopeExtensionFamily R (A) (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R d.right) Empty
        (dgSmallPerfectBaseFamily R (A)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.side))).symm).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso
      (Functor.isoWhiskerLeft (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (D)) CategoryTheory.uliftFunctorTrivial ≪≫
        Functor.rightUnitor _).symm)

/-- 概要：元左代数との同じ比較は完全射。
方針：構成した同値の完全性。規約：同値の底の関手は不変。
使われ方：Cat^perf 内の二因子の比較。 -/
def dgOdotMilnorLaxLeftInputComparison : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap
    (dgKInputStableValue R (dgOdotLeftInput R d)) (dgOdotMilnorLaxLeft R d) :=
  ⟨(dgOdotMilnorLaxLeftInputEquivalence R d).hom,
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_isQCatEquivalence
      (dgOdotMilnorLaxLeftInputEquivalence R d).isQCatEquivalence⟩

/-- 概要：元右代数との同じ比較は完全射。
方針：構成した同値の完全性。規約：同値の底の関手は不変。
使われ方：Cat^perf 内の二因子の比較。 -/
def dgOdotMilnorLaxRightInputComparison : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap
    (dgKInputStableValue R (dgOdotRightInput R d)) (dgOdotMilnorLaxRight R d) :=
  ⟨(dgOdotMilnorLaxRightInputEquivalence R d).hom,
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_isQCatEquivalence
      (dgOdotMilnorLaxRightInputEquivalence R d).isQCatEquivalence⟩

end SerrePositivity.KST.SConstruction
