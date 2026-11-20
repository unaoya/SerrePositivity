module

public meta import SerrePositivity.Util.DeprecatedAlias
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
概要：KST §5、Stacks 080Y の局所支配を大域化する有限アフィン開被覆。
方針：標準アフィン被覆の有限部分被覆の開像を、切断環の Spec による被覆へ戻す。
規約：有限性は被覆の添字型に保持する。
使われ方：アフィン基底の結果を Noether 基底の全体へ貼り合わせる。
-/

@[expose] public noncomputable section

universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/--
概要：準コンパクトなスキームは有限のアフィン開被覆を持つ。
方針：標準アフィン被覆の有限部分被覆の各開像を使う。
規約：KST §5、Stacks 080Y、Noether 性までは要求しない。
使われ方：有限個の局所中心の共通細分。
-/
theorem exists_finite_affineOpenCover (X : Scheme.{u}) [CompactSpace X] :
    ∃ 𝒰 : X.AffineOpenCover.{u}, Finite 𝒰.I₀ := by
  let 𝒰 := X.affineCover.finiteSubcover
  have hAff (i : 𝒰.I₀) : IsAffine (𝒰.X i) := by
    rw [X.affineCover.finiteSubcover_X]
    exact Scheme.isAffine_affineCover X _
  let V (i : 𝒰.I₀) := (𝒰.f i).opensRange
  have hV : ∀ i, IsAffineOpen (V i) := by
    intro i
    have := hAff i
    exact isAffineOpen_opensRange (𝒰.f i)
  let 𝒱 := Scheme.AffineOpenCover.ofIsOpenCover V 𝒰.iSup_opensRange hV
  refine ⟨𝒱, ?_⟩
  change Finite 𝒰.I₀
  infer_instance

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
