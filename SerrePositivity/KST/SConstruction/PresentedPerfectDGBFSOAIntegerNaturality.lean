module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGBFSOANaturality
public import SerrePositivity.KST.SConstruction.KHomotopyFunctor
public import SerrePositivity.KST.SConstruction.SpectrumIntegerComponentEquality

/-! # 同じ実 SOA・新 BF 比較の全整数 π 自然性
概要：元の同じスペクトル比較が誘導する全整数群同型は、通常 dg 入力射に自然。
方針：整数次数の元の段表示へ戻し、全段の基点固定成分の自然性を使う。
規約：同じ実比較射の作用を保つ。使われ方：新 BF K の π₀=K₀ 自然比較。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Spectra
open SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

/-- 同じ実 SOA→新 BF 比較射の全整数 π 作用は、元の通常入力射に自然。 -/
lemma presentedPerfectDGBFSOASpectrumComparison_integer_naturality
    {X Y : PerfDGInput.{u, v} A} (f : X ⟶ Y) (j : ℤ)
    (a : OmegaSpectrum.homotopyGroup
      (kOmegaSpectrum (stableCategoryModel (presentedPerfectDGStableCategory A X))) j) :
    OmegaSpectrum.homotopyMap (presentedPerfectDGBFSOASpectrumComparison A Y) j
        (kHomotopyMap (presentedPerfectDGBFInputStableMap A f) j a) =
      OmegaSpectrum.homotopyMap (presentedPerfectDGBFMap A f) j
        (OmegaSpectrum.homotopyMap (presentedPerfectDGBFSOASpectrumComparison A X) j a) := by
  have h := spectrumHomotopyMap_eq_of_levelwise_component
    (kSpectrumMap (presentedPerfectDGBFInputStableMap A f) ≫
      presentedPerfectDGBFSOASpectrumComparison A Y)
    (presentedPerfectDGBFSOASpectrumComparison A X ≫ presentedPerfectDGBFMap A f)
    (presentedPerfectDGBFSOASpectrumComparison_naturality_component A f) j
  rw [OmegaSpectrum.homotopyMap_comp, OmegaSpectrum.homotopyMap_comp] at h
  exact DFunLike.congr_fun h a

/-- 元の同じ実 SOA 比較射から得る全整数群同型。 -/
def presentedPerfectDGBFSOAGroupEquiv (X : PerfDGInput.{u, v} A) (j : ℤ) :
    OmegaSpectrum.homotopyGroup
        (kOmegaSpectrum (stableCategoryModel (presentedPerfectDGStableCategory A X))) j ≃*
      OmegaSpectrum.homotopyGroup (presentedPerfectDGBFOmegaSpectrum A X) j :=
  (presentedPerfectDGBFSOASpectrumComparison_piIsomorphism A X).groupEquiv j

/-- 同じ整数群同型の順方向は、元の実スペクトル比較射の作用そのもの。 -/
lemma presentedPerfectDGBFSOAGroupEquiv_apply (X : PerfDGInput.{u, v} A) (j : ℤ)
    (a : OmegaSpectrum.homotopyGroup
      (kOmegaSpectrum (stableCategoryModel (presentedPerfectDGStableCategory A X))) j) :
    presentedPerfectDGBFSOAGroupEquiv A X j a =
      OmegaSpectrum.homotopyMap (presentedPerfectDGBFSOASpectrumComparison A X) j a := rfl

/-- 元の同じ実比較による全整数群同型は、通常 dg 入力射に自然。 -/
lemma presentedPerfectDGBFSOAGroupEquiv_naturality
    {X Y : PerfDGInput.{u, v} A} (f : X ⟶ Y) (j : ℤ)
    (a : OmegaSpectrum.homotopyGroup
      (kOmegaSpectrum (stableCategoryModel (presentedPerfectDGStableCategory A X))) j) :
    presentedPerfectDGBFSOAGroupEquiv A Y j
        (kHomotopyMap (presentedPerfectDGBFInputStableMap A f) j a) =
      OmegaSpectrum.homotopyMap (presentedPerfectDGBFMap A f) j
        (presentedPerfectDGBFSOAGroupEquiv A X j a) :=
  presentedPerfectDGBFSOASpectrumComparison_integer_naturality A f j a

end SerrePositivity.KST.SConstruction
