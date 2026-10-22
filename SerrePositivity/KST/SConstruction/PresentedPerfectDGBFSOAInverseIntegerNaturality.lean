module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGBFSOAIntegerNaturality
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGBFDGKComparison

/-! # 同じ実 BF 逆比較の整数 π 自然性
概要：元の逆方向 BF 射は、同じ SOA 群同型の逆として全整数 π に自然に作用する。
方針：実射の全段の右逆成分を整数 π へ送り、順方向比較の自然性で反映する。
規約：別の群同型に置換しない。使われ方：元の dgK への実比較の入力自然性。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Spectra
open SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

/-- 元の実逆方向 BF 射の作用は、同じ実 SOA 群同型の逆を回収する。 -/
lemma presentedPerfectDGBFSOAInverseComparison_integer_apply
    (X : PerfDGInput.{u, v} A) (j : ℤ)
    (a : OmegaSpectrum.homotopyGroup (presentedPerfectDGBFOmegaSpectrum A X) j) :
    OmegaSpectrum.homotopyMap (presentedPerfectDGBFSOAInverseComparison A X) j a =
      (presentedPerfectDGBFSOAGroupEquiv A X j).symm a := by
  have h := spectrumHomotopyMap_eq_of_levelwise_component
    (presentedPerfectDGBFSOAInverseComparison A X ≫
      presentedPerfectDGBFSOASpectrumComparison A X) (𝟙 _)
    (fun n => OmegaSpectrum.levelwiseInverse_right_component _
      (presentedPerfectDGBFSOASpectrumComparison_levelwise A X) n) j
  rw [OmegaSpectrum.homotopyMap_comp, OmegaSpectrum.homotopyMap_id] at h
  apply (presentedPerfectDGBFSOAGroupEquiv A X j).injective
  exact (DFunLike.congr_fun h a).trans
    ((presentedPerfectDGBFSOAGroupEquiv A X j).apply_symm_apply a).symm

/-- 同じ実逆方向比較の全整数 π 作用は、元の通常 dg 入力射に自然。 -/
lemma presentedPerfectDGBFSOAInverseComparison_integer_naturality
    {X Y : PerfDGInput.{u, v} A} (f : X ⟶ Y) (j : ℤ)
    (a : OmegaSpectrum.homotopyGroup (presentedPerfectDGBFOmegaSpectrum A X) j) :
    OmegaSpectrum.homotopyMap (presentedPerfectDGBFSOAInverseComparison A Y) j
        (OmegaSpectrum.homotopyMap (presentedPerfectDGBFMap A f) j a) =
      kHomotopyMap (presentedPerfectDGBFInputStableMap A f) j
        (OmegaSpectrum.homotopyMap (presentedPerfectDGBFSOAInverseComparison A X) j a) := by
  rw [presentedPerfectDGBFSOAInverseComparison_integer_apply,
    presentedPerfectDGBFSOAInverseComparison_integer_apply]
  apply (presentedPerfectDGBFSOAGroupEquiv A Y j).injective
  rw [MulEquiv.apply_symm_apply]
  have h := presentedPerfectDGBFSOAGroupEquiv_naturality A f j
    ((presentedPerfectDGBFSOAGroupEquiv A X j).symm a)
  rw [MulEquiv.apply_symm_apply] at h
  exact h.symm

end SerrePositivity.KST.SConstruction
