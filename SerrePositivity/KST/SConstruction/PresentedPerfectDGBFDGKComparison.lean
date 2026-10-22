module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGBFSOASpectrumComparison
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGBFEvaluationComparison
public import SerrePositivity.KST.Spectra.SpectrumLevelwiseInverse

/-! # 実 BF 厳密豊穣 K から元の dgK への実比較
概要：新 BF K と元の dgK を、実スペクトル射と全整数 π 同型で比較する。
方針：同じ Perf の SOA 比較の逆方向 BF 射と、元の実 Perf 評価射を合成する。
規約：比較の入力自然性と Morita の新関手への移送は別工程。使われ方：K-4d の同定。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Spectra
open SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

/-- 新 BF K から、同じラベル付き Perf の旧 BF K への実逆方向比較。 -/
def presentedPerfectDGBFSOAInverseComparison (C : PerfDGInput.{u, v} A) :
    presentedPerfectDGBFOmegaSpectrum A C ⟶
      kOmegaSpectrum (stableCategoryModel (presentedPerfectDGStableCategory A C)) :=
  OmegaSpectrum.levelwiseInverse (presentedPerfectDGBFSOASpectrumComparison A C)
    (presentedPerfectDGBFSOASpectrumComparison_levelwise A C)

/-- 同じ実逆方向比較は全整数次数で π 同型。 -/
lemma presentedPerfectDGBFSOAInverseComparison_piIsomorphism (C : PerfDGInput.{u, v} A) :
    OmegaSpectrum.PiIsomorphism (presentedPerfectDGBFSOAInverseComparison A C) :=
  OmegaSpectrum.levelwiseInverse_piIsomorphism _
    (presentedPerfectDGBFSOASpectrumComparison_levelwise A C)

/-- 新しい元の実 BF K から、元の dgK への実際のスペクトル比較射。 -/
def presentedPerfectDGBFDGKComparison (C : PerfDGInput.{u, v} A) :
    presentedPerfectDGBFOmegaSpectrum A C ⟶ dgK A C :=
  presentedPerfectDGBFSOAInverseComparison A C ≫ presentedPerfectDGBFEvaluationKMap A C

/-- 同じ元の dgK への実比較射は全整数次数で π 同型。 -/
lemma presentedPerfectDGBFDGKComparison_piIsomorphism (C : PerfDGInput.{u, v} A) :
    OmegaSpectrum.PiIsomorphism (presentedPerfectDGBFDGKComparison A C) :=
  (presentedPerfectDGBFSOAInverseComparison_piIsomorphism A C).comp
    (presentedPerfectDGBFEvaluationKMap_piIsomorphism A C)

/-- 新 BF K の整数 K 群と元の dgK 群の同型は、同じ実比較射の作用。 -/
def presentedPerfectDGBFDGKGroupEquiv (C : PerfDGInput.{u, v} A) (j : ℤ) :
    OmegaSpectrum.homotopyGroup (presentedPerfectDGBFOmegaSpectrum A C) j ≃* dgKGroup A C j :=
  (presentedPerfectDGBFDGKComparison_piIsomorphism A C).groupEquiv j

/-- 同じ整数群比較の順方向は、元の実スペクトル比較射の作用を回収する。 -/
lemma presentedPerfectDGBFDGKGroupEquiv_apply (C : PerfDGInput.{u, v} A) (j : ℤ)
    (a : OmegaSpectrum.homotopyGroup (presentedPerfectDGBFOmegaSpectrum A C) j) :
    presentedPerfectDGBFDGKGroupEquiv A C j a =
      OmegaSpectrum.homotopyMap (presentedPerfectDGBFDGKComparison A C) j a := rfl

end SerrePositivity.KST.SConstruction
