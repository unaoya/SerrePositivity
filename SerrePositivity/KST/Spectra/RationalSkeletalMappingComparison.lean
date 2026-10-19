module

public import SerrePositivity.KST.Spectra.SkeletalMappingDetection
public import SerrePositivity.KST.Spectra.RationalSkeletalMittagLeffler

/-!
概要：有限群の有理写像空間の高次群の骨格の塔への比較と一骨格での検出。
方針：実際の有理化各段の cohomology 消滅を通常の写像空間の比較へ入力する。
規約：最初の fiber の計算と全整数次数への移送は別工程。
使われ方：Goerss–Jardine VIII §2、BF 1978 §2。有理 Shapiro の全射性の準備。
-/

@[expose] public section
universe u
open CategoryTheory SSet Opposite

namespace SerrePositivity.KST.Spectra.RationalSkeletalTower

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 実際の有理写像空間の高次群と骨格各段の群の逆極限の比較は全単射。 -/
theorem mappingGroupComparison_bijective (X : OmegaSpectrum.{u}) (k : ℕ)
    (G : Type u) [Group G] [Finite G] (r : ℕ) :
    let K := nerve (AsSmall.{u} (SingleObj G))
    let Y := ((OmegaSpectrum.rationalization X).level k).space
    Function.Bijective (UnbasedPointedMapping.groupComparison K Y (r + 1)) :=
  (UnbasedPointedMapping.mappingGroupEquivOfCohomologyIsZero _ _ r
    (fun n ↦ correction_cohomology_isZero X k G n r)).bijective

/-- 実際の有理写像空間の高次群の一骨格への制限は単射。 -/
theorem stageOneGroupMap_injective (X : OmegaSpectrum.{u}) (k : ℕ)
    (G : Type u) [Group G] [Finite G] (r : ℕ) :
    let K := nerve (AsSmall.{u} (SingleObj G))
    let Y := ((OmegaSpectrum.rationalization X).level k).space
    Function.Injective (pointedGroupMap (X := UnbasedPointedMapping.obj K Y) (r + 1)
      ((UnbasedPointedMapping.cone K Y).π.app (op 1))) :=
  UnbasedPointedMapping.stageOneGroupMap_injective_of_isZero _ _ r
    (fun n ↦ correction_cohomology_isZero X k G n r)

end
end SerrePositivity.KST.Spectra.RationalSkeletalTower
