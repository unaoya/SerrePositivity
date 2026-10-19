module

public import SerrePositivity.KST.Spectra.SkeletalInitialDetection
public import SerrePositivity.KST.Spectra.RationalSkeletalMappingComparison

/-!
概要：有限群の有理写像空間の高次群は零骨格への制限で検出できる。
方針：群の nerve の一つの頂点と H¹ 消滅を、既証の高次 cohomology の計算へ追加する。
規約：通常の写像空間の群について述べる。整数次数への移送は別工程。
使われ方：Goerss–Jardine VIII §2、BF 1978 §2。有理 Shapiro の全射性への入力。
-/

@[expose] public section
universe u
open CategoryTheory Limits SSet Opposite

namespace SerrePositivity.KST.Spectra.RationalSkeletalTower

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 最初の fiber の核を消す、実際の有理係数の H¹ の消滅。 -/
theorem first_cohomology_isZero (X : OmegaSpectrum.{u}) (k : ℕ)
    (G : Type u) [Group G] [Finite G] (r : ℕ) :
    IsZero ((NormalizedValueCochains.complex (nerve (AsSmall.{u} (SingleObj G)))
      (AddCommGrpCat.of (SkeletalCellAttachment.positiveAdditiveCoefficient
        ((OmegaSpectrum.rationalization X).level k).space 0 r))).homology 1) :=
  RationalLevelNormalizedCochains.positive_cohomology_isZero X k G (0 + 1 + r) 0

/-- 実際の有理写像空間の高次群の零骨格への制限は単射。 -/
theorem stageZeroGroupMap_injective (X : OmegaSpectrum.{u}) (k : ℕ)
    (G : Type u) [Group G] [Finite G] (r : ℕ) :
    let K := nerve (AsSmall.{u} (SingleObj G))
    let Y := ((OmegaSpectrum.rationalization X).level k).space
    Function.Injective (pointedGroupMap (X := UnbasedPointedMapping.obj K Y) (r + 1)
      ((UnbasedPointedMapping.cone K Y).π.app (op 0))) :=
  UnbasedPointedMapping.stageZeroGroupMap_injective_of_isZero _ _ r
    (first_cohomology_isZero X k G r) (fun n ↦ correction_cohomology_isZero X k G n r)

end
end SerrePositivity.KST.Spectra.RationalSkeletalTower
