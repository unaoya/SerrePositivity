module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGEvaluationIntegerNaturality
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGBFSOAInverseIntegerNaturality

/-! # 新 BF K と元の dgK の同じ実比較の整数 π 自然性
概要：構成済みの実スペクトル比較射による全整数群同型は、厳密 dg 入力射に自然。
方針：同じ SOA 逆比較の自然性と、元の実 Perf 評価の自然性を合成する。
規約：比較射そのものの作用を回収する。使われ方：K-4d の dg 関手性との同定。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Spectra
open SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

/-- 新 BF K→元の dgK の同じ実比較射は、全整数 π で通常 dg 入力射に自然。 -/
lemma presentedPerfectDGBFDGKComparison_integer_naturality
    {X Y : PerfDGInput.{u, v} A} (f : X ⟶ Y) (j : ℤ)
    (a : OmegaSpectrum.homotopyGroup (presentedPerfectDGBFOmegaSpectrum A X) j) :
    OmegaSpectrum.homotopyMap (dgKMap A X Y f.down) j
        (OmegaSpectrum.homotopyMap (presentedPerfectDGBFDGKComparison A X) j a) =
      OmegaSpectrum.homotopyMap (presentedPerfectDGBFDGKComparison A Y) j
        (OmegaSpectrum.homotopyMap (presentedPerfectDGBFMap A f) j a) := by
  simp only [presentedPerfectDGBFDGKComparison, OmegaSpectrum.homotopyMap_comp,
    MonoidHom.comp_apply]
  exact (presentedPerfectDGBFEvaluation_integer_naturality A f j _).trans
    (congrArg (OmegaSpectrum.homotopyMap (presentedPerfectDGBFEvaluationKMap A Y) j)
      (presentedPerfectDGBFSOAInverseComparison_integer_naturality A f j a).symm)

/-- 同じ実比較射の整数群同型は、元の dgKMap と同じ新 BF 射について自然。 -/
lemma presentedPerfectDGBFDGKGroupEquiv_naturality
    {X Y : PerfDGInput.{u, v} A} (f : X ⟶ Y) (j : ℤ)
    (a : OmegaSpectrum.homotopyGroup (presentedPerfectDGBFOmegaSpectrum A X) j) :
    OmegaSpectrum.homotopyMap (dgKMap A X Y f.down) j
        (presentedPerfectDGBFDGKGroupEquiv A X j a) =
      presentedPerfectDGBFDGKGroupEquiv A Y j
        (OmegaSpectrum.homotopyMap (presentedPerfectDGBFMap A f) j a) :=
  presentedPerfectDGBFDGKComparison_integer_naturality A f j a

end SerrePositivity.KST.SConstruction
