module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGBFDGKComparison
public import SerrePositivity.KST.SConstruction.KSpectrumConnectivity
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.HomotopyComponents

/-! # 同じ厳密 dg BF K の正段連結性と負次数消滅
概要：厳密豊穣化した実 BF K も、連結 K の全負整数群消滅を満たす。
方針：同じ実 SOA 比較で正段の連結性を移し、元の dgK への実群同型で負次数を反映する。
規約：零空間の連結性は主張しない。使われ方：L1c と BGT 非連結化の入力の区別。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet Spectra
open SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

/-- 同じ実 BF K の全ての正の段は連結。 -/
instance presentedPerfectDGBFOmegaSpectrum_positive_isConnected
    (X : PerfDGInput.{u, v} A) (r : ℕ) :
    SSet.IsConnected (((presentedPerfectDGBFOmegaSpectrum A X).level (r + 1)).space).right := by
  let C := stableCategoryModel (presentedPerfectDGStableCategory A X)
  let f := (presentedPerfectDGBFSOASpectrumComparison A X).app (r + 1)
  have hs := (presentedPerfectDGBFSOASpectrumComparison_levelwise A X (r + 1)).piZero_bijective_at
    (((kOmegaSpectrum C).level (r + 1)).space).basepoint
  let : SSet.IsPreconnected
      (((presentedPerfectDGBFOmegaSpectrum A X).level (r + 1)).space).right := ⟨by
    intro a b
    obtain ⟨x, rfl⟩ := hs.surjective a
    obtain ⟨y, rfl⟩ := hs.surjective b
    exact congrArg (SSet.mapπ₀ f.right) (Subsingleton.elim x y)⟩
  exact ⟨⟨(((presentedPerfectDGBFOmegaSpectrum A X).level (r + 1)).space).basepoint⟩⟩

/-- 新しい元の実 BF K の全負整数次数のホモトピー群は一点。 -/
lemma presentedPerfectDGBFOmegaSpectrum_negative_subsingleton
    (X : PerfDGInput.{u, v} A) (j : ℤ) (hj : j < 0) :
    Subsingleton (OmegaSpectrum.homotopyGroup (presentedPerfectDGBFOmegaSpectrum A X) j) := by
  let : Subsingleton (dgKGroup A X j) :=
    kOmegaSpectrum_negative_subsingleton (perfectDGStableModel A X Set.univ) j hj
  exact (presentedPerfectDGBFDGKGroupEquiv A X j).injective.subsingleton

/-- 同じ実 BF K の任意の負整数次数の要素は単位。 -/
lemma presentedPerfectDGBFOmegaSpectrum_negative_eq_one
    (X : PerfDGInput.{u, v} A) (j : ℤ) (hj : j < 0)
    (a : OmegaSpectrum.homotopyGroup (presentedPerfectDGBFOmegaSpectrum A X) j) : a = 1 := by
  let := presentedPerfectDGBFOmegaSpectrum_negative_subsingleton A X j hj
  exact Subsingleton.elim _ _

end SerrePositivity.KST.SConstruction
