module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGBFDGKComparison
public import SerrePositivity.KST.SConstruction.SpectrumIntegerComponentEquality

/-!
概要：元の SOA と固定 BF K の順逆比較が、同じ整数 π 上で互いに逆であることを保持する。
方針：正本の各段の点つき逆ホモトピーを、元のスペクトルの整数 π へ渡す。
規約：厳密射の合成を恒等とは主張しない。固定 K・元の BF 比較を変更しない。
使われ方：K-7 d4 の選択比較の合成で、中間の実 BF 比較を整数 π 上で縮約する。
-/
@[expose] public noncomputable section
universe u v
open CategoryTheory
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.NonConnective

private theorem comparisonInversePi_left {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y)
    (hf : ∀ n, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (f.app n).right) (j : ℤ) :
    (OmegaSpectrum.homotopyMap (OmegaSpectrum.levelwiseInverse f hf) j).comp
      (OmegaSpectrum.homotopyMap f j) = MonoidHom.id _ := by
  have h := spectrumHomotopyMap_eq_of_levelwise_component
    (f ≫ OmegaSpectrum.levelwiseInverse f hf) (𝟙 X)
    (OmegaSpectrum.levelwiseInverse_left_component f hf) j
  simpa only [OmegaSpectrum.homotopyMap_comp, OmegaSpectrum.homotopyMap_id] using h

private theorem comparisonInversePi_right {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y)
    (hf : ∀ n, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (f.app n).right) (j : ℤ) :
    (OmegaSpectrum.homotopyMap f j).comp
      (OmegaSpectrum.homotopyMap (OmegaSpectrum.levelwiseInverse f hf) j) = MonoidHom.id _ := by
  have h := spectrumHomotopyMap_eq_of_levelwise_component
    (OmegaSpectrum.levelwiseInverse f hf ≫ f) (𝟙 Y)
    (OmegaSpectrum.levelwiseInverse_right_component f hf) j
  simpa only [OmegaSpectrum.homotopyMap_comp, OmegaSpectrum.homotopyMap_id] using h

variable (R : Type u) [CommRing R] (A : PerfDGInput.{u, v} R) (j : ℤ)

/-- SOA K から始めた元の順逆比較は、同じ全整数 π 上で恒等となる。 -/
theorem dgKappaFixedKComparisonPi_left :
    (OmegaSpectrum.homotopyMap (presentedPerfectDGBFSOAInverseComparison R A) j).comp
      (OmegaSpectrum.homotopyMap (presentedPerfectDGBFSOASpectrumComparison R A) j) =
        MonoidHom.id _ :=
  comparisonInversePi_left (presentedPerfectDGBFSOASpectrumComparison R A)
    (presentedPerfectDGBFSOASpectrumComparison_levelwise R A) j

/-- 固定 BF K から始めた元の逆順比較も、同じ全整数 π 上で恒等となる。 -/
theorem dgKappaFixedKComparisonPi_right :
    (OmegaSpectrum.homotopyMap (presentedPerfectDGBFSOASpectrumComparison R A) j).comp
      (OmegaSpectrum.homotopyMap (presentedPerfectDGBFSOAInverseComparison R A) j) =
        MonoidHom.id _ :=
  comparisonInversePi_right (presentedPerfectDGBFSOASpectrumComparison R A)
    (presentedPerfectDGBFSOASpectrumComparison_levelwise R A) j

end SerrePositivity.KST.NonConnective
