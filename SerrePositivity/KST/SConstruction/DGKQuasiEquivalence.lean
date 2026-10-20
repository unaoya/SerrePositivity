module
public import SerrePositivity.KST.SConstruction.DGKTheory

/-! # 厳密 dg 準同値から実 BF K の Morita 比較へ
概要：入力 dg 関手の準同値条件を、実 Perf 延長と実 BF K 射に直接渡す。
方針：元の主 Perf 延長を順方向とする既存の同値を使い、Morita 判定を適用する。
規約：準同値は Morita 同値の十分条件。使われ方：K-4d の模型変更の不変性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SerrePositivity.DifferentialGraded Spectra
section Perfect
variable (A : Type u) [CommRing A] (D : Type v) (E : Type w)
  [DGCategory A D] [Small.{u} D] [DGCategory A E] [Small.{u} E]
  (F : DGFunctor A D E) (hF : QuasiEquivalence F)

include hF

/-- 入力の準同値から、元の実 Perf dg 延長の全 Hom の擬同型と H⁰ 同値を得る。 -/
lemma perfectDGExtension_quasiEquivalence_of_quasiEquivalence :
    QuasiEquivalence (perfectDGExtension A D E F) := by
  let : (quasiEquivalencePerfectExtension A D E F).IsEquivalence :=
    (quasiEquivalencePerfectEquivalence A D E F hF).isEquivalence_functor
  exact perfectDGExtension_quasiEquivalence A D E F

end Perfect

variable (A : Type u) [CommRing A] (D E : Type v)
  [DGCategory A D] [Small.{u} D] [DGCategory A E] [Small.{u} E]
  (F : DGFunctor A D E) (hF : QuasiEquivalence F)

include hF

/-- 任意の厳密 dg 準同値の元の BF K 射は全整数次数で π_* 同型。 -/
lemma dgKMap_piIsomorphism_of_quasiEquivalence :
    OmegaSpectrum.PiIsomorphism (dgKMap A D E F) := by
  let : (quasiEquivalencePerfectExtension A D E F).IsEquivalence :=
    (quasiEquivalencePerfectEquivalence A D E F hF).isEquivalence_functor
  exact dgKMap_piIsomorphism A D E F

/-- 厳密 dg 準同値に対する実 BF K 群の同型。順方向は同じ元の BF 射の作用。 -/
def dgKQuasiEquivalenceGroupEquiv (j : ℤ) : dgKGroup A D j ≃* dgKGroup A E j :=
  (dgKMap_piIsomorphism_of_quasiEquivalence A D E F hF).groupEquiv j

/-- 準同値比較は元の厳密 dg 関手による BF K 射を回収する。 -/
lemma dgKQuasiEquivalenceGroupEquiv_apply (j : ℤ) (a : dgKGroup A D j) :
    dgKQuasiEquivalenceGroupEquiv A D E F hF j a =
      OmegaSpectrum.homotopyMap (dgKMap A D E F) j a := rfl

end SerrePositivity.KST.SConstruction
