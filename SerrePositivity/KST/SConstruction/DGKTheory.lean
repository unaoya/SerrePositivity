module
public import SerrePositivity.KST.SConstruction.KSpectrumInvariance
public import SerrePositivity.KST.SConstruction.PerfectDGMoritaRealization

/-! # 厳密 dg 入力の実 BF K スペクトルと Morita 不変性
概要：一般の小さい dg 圏の実 Perf 模型から連結 BF K を定義する。
方針：実 graph 延長の完全性を使い、主 Perf 作用の同値から全整数 π_* 同型を得る。
規約：入力の恒等・合成の厳密豊穣法則は別工程。使われ方：K-4d と後続の非連結化。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Spectra SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D E : Type v)
  [DGCategory A D] [Small.{u} D] [DGCategory A E] [Small.{u} E]

/-- 小さい dg 圏の実射影的 Perf による連結 BF K スペクトル。 -/
def dgK : OmegaSpectrum.{max (u + 1) v} := kOmegaSpectrum (perfectDGStableModel A D Set.univ)

/-- 元の厳密 dg 関手の実 graph 延長から構成した、実 BF K スペクトルの射。 -/
def dgKMap (F : DGFunctor A D E) : dgK A D ⟶ dgK A E :=
  kSpectrumMap (perfectDGStableMap A D E F)

/-- 実 BF dg K スペクトルの全整数次数の群。 -/
abbrev dgKGroup (j : ℤ) := OmegaSpectrum.homotopyGroup (dgK A D) j

variable (F : DGFunctor A D E) [(quasiEquivalencePerfectExtension A D E F).IsEquivalence]

/-- 主 Perf 作用が同値な厳密 dg 関手の元の実 BF K 射は全整数 π_* 同型。 -/
lemma dgKMap_piIsomorphism : OmegaSpectrum.PiIsomorphism (dgKMap A D E F) :=
  kSpectrumMap_piIsomorphism_of_realization (perfectDGStableMap A D E F)
    (fun r => perfectDGMoritaRealization_localized_isIso A D E F r)

/-- Morita 同値が誘導する実 BF K 群の同型。順方向は元のスペクトルの射の作用。 -/
def dgKMoritaGroupEquiv (j : ℤ) : dgKGroup A D j ≃* dgKGroup A E j :=
  (dgKMap_piIsomorphism A D E F).groupEquiv j

/-- Morita 比較の順方向は元の同じ厳密 dg 関手による実 BF K 射を回収する。 -/
lemma dgKMoritaGroupEquiv_apply (j : ℤ) (a : dgKGroup A D j) :
    dgKMoritaGroupEquiv A D E F j a = OmegaSpectrum.homotopyMap (dgKMap A D E F) j a := rfl

end SerrePositivity.KST.SConstruction
