module

public import SerrePositivity.KST.NonConnective.NonnegativeBoundaryComparison
public import SerrePositivity.KST.SConstruction.KSpectrumConnectivity

/-!
概要：既存 S• の連結 BF K の同じ三つの実評価射に対する整数 π 加法性。
方針：非負次数は自然な一重境界商比較で移し、負次数は既存の連結性を使う。
規約：一般安定 ∞ 圏上の非連結 K は定義しない。
使われ方：厳密 dg cone の固定 BF K の swindle の消去。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.KST.SConstruction SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.NonConnective

/-- 元の連結 BF K の非負整数群上で、中央項の評価は両端の評価の積。 -/
theorem connectedKMiddle_additivity_nonnegative (X : StableModel.{u}) (n : ℕ)
    (a : OmegaSpectrum.homotopyGroup (kOmegaSpectrum (cofiberStableModel X)) (n : ℤ)) :
    kHomotopyMap (cofiberStableMiddle X) (n : ℤ) a =
      kHomotopyMap (cofiberStableSubobject X) (n : ℤ) a *
        kHomotopyMap (cofiberStableQuotient X) (n : ℤ) a := by
  apply (nonnegativeBoundaryEquiv X n).injective
  rw [map_mul, nonnegativeBoundaryEquiv_naturality,
    nonnegativeBoundaryEquiv_naturality, nonnegativeBoundaryEquiv_naturality]
  exact singleBoundaryMiddle_additivity X n (nonnegativeBoundaryEquiv _ n a)

/-- 元の連結 BF K の全整数群で、同じ実評価射の加法性が成立する。 -/
theorem connectedKMiddle_additivity (X : StableModel.{u}) (j : ℤ)
    (a : OmegaSpectrum.homotopyGroup (kOmegaSpectrum (cofiberStableModel X)) j) :
    kHomotopyMap (cofiberStableMiddle X) j a =
      kHomotopyMap (cofiberStableSubobject X) j a *
        kHomotopyMap (cofiberStableQuotient X) j a := by
  cases j with
  | ofNat n => exact connectedKMiddle_additivity_nonnegative X n a
  | negSucc n =>
    have := kOmegaSpectrum_negative_subsingleton X (Int.negSucc n) (by omega)
    exact Subsingleton.elim _ _

end SerrePositivity.KST.NonConnective
