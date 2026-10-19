module

public import SerrePositivity.KST.Comparison.LocalCoefficientColimits
public import Mathlib.CategoryTheory.Presentable.Comma
public import Mathlib.CategoryTheory.Presentable.IsDiscrete

/-!
# 基底上の有限表示可能な単体集合

概要：下の単体集合が有限表示可能なら、基底上の対象も有限表示可能である。
方針：comma 圏の有限表示可能性の定理を恒等関手と一点からの関手へ適用する。
規約：Waldhausen LNM 1126 §1.7・§1.8 の局所係数の horn 添付。
使われ方：slice の horn 生成射に小対象構成を適用する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory CategoryTheory.Limits
attribute [local instance] Cardinal.fact_isRegular_aleph0

/--
概要：有限表示可能な単体集合を始域に持つ基底上の対象は有限表示可能である。
方針：comma 圏の恒等関手と一点からの関手の定理を使う。
規約：基底自体の有限性は要求しない。
使われ方：基底上の horn の有限表示可能性。
-/
theorem over_isFinitelyPresentable_of_left {B : SSet.{u}} (X : Over B)
    [IsFinitelyPresentable.{u} X.left] : IsFinitelyPresentable.{u} X := by
  change IsCardinalPresentable X Cardinal.aleph0
  exact Comma.isCardinalPresentable_mk (F₁ := 𝟭 SSet.{u})
    (F₂ := Functor.fromPUnit B) (κ := Cardinal.aleph0)
    (X₁ := X.left) (X₂ := X.right) X.hom

end SerrePositivity.KST.Comparison
