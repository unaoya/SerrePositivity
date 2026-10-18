module

public import SerrePositivity.KST.Spectra.TrivialFixedPointRetraction
public import SerrePositivity.KST.Spectra.SpectrumBoundary

/-!
概要：自明作用の hG への標準比較の整数次数ホモトピー群での単射性。
方針：十分高い段の正次数群での単射性を自然な段表示で移す。
規約：全射性、有理性、有限性の仮定は含めない。
使われ方：Goerss–Jardine VIII §2、BF 1978 §2、HA §1.4.2。有理 Shapiro の単射側。
-/

@[expose] public section

universe u

open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：自明作用から hG への標準射は全整数次数の π_* で単射。
方針：正次数を計算する段の自然性と、その段の評価の左逆を使う。
規約：任意の群と任意の BF Ω スペクトルで成り立つ。
使われ方：Goerss–Jardine VIII §2、BF 1978 §2。有理 Shapiro の単射性。 -/
theorem homotopyFixedPointsUnit_homotopyMap_injective (G : Type u) [Group G]
    (X : OmegaSpectrum.{u}) (j : ℤ) :
    Function.Injective (OmegaSpectrum.homotopyMap (homotopyFixedPointsUnit G X) j) := by
  let k := OmegaSpectrum.boundaryStage j
  let r := OmegaSpectrum.boundaryIndex j
  let hk := OmegaSpectrum.boundaryStage_admissible j
  let hd := OmegaSpectrum.boundaryStage_degree j
  intro a b h
  apply (OmegaSpectrum.positiveStageEquiv X j k r hk hd).injective
  apply homotopyFixedPointsUnit_level_groupMap_injective G X k r
  have ht := congrArg
    (OmegaSpectrum.positiveStageEquiv (homotopyFixedPoints (Action.trivial G X)) j k r hk hd) h
  simpa only [OmegaSpectrum.positiveStageEquiv_natural, pointedGroupMap] using ht

end

end SerrePositivity.KST.Spectra
