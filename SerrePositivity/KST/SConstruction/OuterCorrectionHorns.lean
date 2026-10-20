module
public import SerrePositivity.KST.SConstruction.OuterCorrectionCorners

/-! # 元の外側二部分三角形を貼る二つの全内ホーン
概要：正規化出口と元の隣接全辺を、同じ実複体内の二つの全内ホーンへまとめる。
方針：証明済みの同じ共有頂点と内ホーンの pushout の普遍性を使う。
規約：元の四つの全区間を厳密に保持し、新しい辺を選ばない。
使われ方：元の左右外側二部分三角形全体の同じホーンへの接続。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open scoped Simplicial

/-- 左正規化出口と元の交換下面を同じ共有頂点で貼った全内ホーン。 -/
def correctionOuterLeftHorn : (Λ[2, 1] : SSet.{u}) ⟶ correctionNormalizationPasting :=
  horn₂₁.isPushout.desc correctionNormalizationPastingLeftTarget correctionOuterLeftSecond
    correctionOuterLeft_corner

/-- 元の最初の補正辺と右正規化出口を同じ共有頂点で貼った全内ホーン。 -/
def correctionOuterRightHorn : (Λ[2, 1] : SSet.{u}) ⟶ correctionNormalizationPasting :=
  horn₂₁.isPushout.desc correctionOuterRightFirst correctionNormalizationPastingRightTarget
    correctionOuterRight_corner

/-- 左ホーンの元の第一全辺を厳密に回収する。 -/
lemma correctionOuterLeftHorn_first :
    horn₂₁.ι₀₁ ≫ correctionOuterLeftHorn.{u} = correctionNormalizationPastingLeftTarget :=
  horn₂₁.isPushout.inl_desc _ _ _

/-- 左ホーンの元の第二全辺を厳密に回収する。 -/
lemma correctionOuterLeftHorn_second :
    horn₂₁.ι₁₂ ≫ correctionOuterLeftHorn.{u} = correctionOuterLeftSecond :=
  horn₂₁.isPushout.inr_desc _ _ _

/-- 右ホーンの元の第一全辺を厳密に回収する。 -/
lemma correctionOuterRightHorn_first :
    horn₂₁.ι₀₁ ≫ correctionOuterRightHorn.{u} = correctionOuterRightFirst :=
  horn₂₁.isPushout.inl_desc _ _ _

/-- 右ホーンの元の第二全辺を厳密に回収する。 -/
lemma correctionOuterRightHorn_second :
    horn₂₁.ι₁₂ ≫ correctionOuterRightHorn.{u} = correctionNormalizationPastingRightTarget :=
  horn₂₁.isPushout.inr_desc _ _ _

end SerrePositivity.KST.SConstruction
