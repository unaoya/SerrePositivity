module
public import SerrePositivity.KST.SConstruction.DGOdotTargetSmallPerfect
public import SerrePositivity.KST.SConstruction.DGAlgebraEnvelopeYonedaMorita
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGQuasiEquivalenceNerve

/-! # 元の終域から同じ cone 小模型への Yoneda の Morita 比較
概要：元の終域の同じ厳密 Yoneda は、同じ実一回 Perf 延長で同値を与える。
方針：D の自由生成 API を使う包絡模型の定理を、同じ評価済み cone 族へ適用する。
規約：生成条件を追加仮定にしない。使われ方：具体的 ⊙ 比較の終域と固定 S の接続。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "E" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R (DGOdotInput.corner d)
local notation "b" => (Opposite.op _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraPoint.star : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R (DGOdotInput.corner d))

/-- 元の自由代表が、同じ cone 点を含む実小模型の全 Perf を生成する。 -/
lemma dgOdotTargetSmallPerfect_perfectOver_representable_eq :
    modulePerfectOver R (DGOdotTargetSmallPerfect R d)
      {dgSmallPerfectEnvelopeRepresentable R (E) PUnit.{1} (dgOdotTargetConeFamily R d) (b)} =
    modulePerfect R (DGOdotTargetSmallPerfect R d) :=
  dgAlgebraEnvelope_perfectOver_representable_eq R d.corner PUnit.{1}
    (dgOdotTargetConeFamily R d) (b)

/-- 元の厳密 Yoneda の同じ主 Perf 延長は、追加の生成仮定なしで同値。 -/
lemma dgOdotTargetSmallYoneda_isMorita :
    (quasiEquivalencePerfectExtension R (E) (DGOdotTargetSmallPerfect R d)
      (dgOdotTargetSmallYoneda R d)).IsEquivalence :=
  dgAlgebraEnvelopeYoneda_isMorita R d.corner PUnit.{1} (dgOdotTargetConeFamily R d)

/-- 同じ元の Yoneda の一回 dg Perf 延長は、元の全 Hom 作用による準同値。 -/
lemma dgOdotTargetSmallYoneda_perfectDG_quasiEquivalence :
    QuasiEquivalence (perfectDGExtension R (E) (DGOdotTargetSmallPerfect R d)
      (dgOdotTargetSmallYoneda R d)) :=
  dgAlgebraEnvelopeYoneda_perfectDG_quasiEquivalence R d.corner PUnit.{1}
    (dgOdotTargetConeFamily R d)

/-- 同じ元の一回 dg Perf 延長を順方向に持つ、実 native nerve 同値。 -/
def dgOdotTargetSmallYonedaPerfectNerveEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (PerfectDGModule R (E)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (PerfectDGModule R (DGOdotTargetSmallPerfect R d))) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuasiEquivalenceNerveEquivalence
    (perfectDGExtension R (E) (DGOdotTargetSmallPerfect R d) (dgOdotTargetSmallYoneda R d))
    (dgOdotTargetSmallYoneda_perfectDG_quasiEquivalence R d)

end SerrePositivity.KST.SConstruction
