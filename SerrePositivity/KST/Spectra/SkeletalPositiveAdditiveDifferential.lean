module

public import SerrePositivity.KST.Spectra.SkeletalCoefficientAlternatingAll
public import SerrePositivity.KST.Spectra.SkeletalAdditiveCoefficientDifferential

/-!
概要：全ての正次数 cochain の実際の係数微分の加法表示と通常の核・像の一致。
方針：次数一を含む交代式を加法準同型の等式へ束ね、符号が核と像を保つことを使う。
規約：cochain 次数は一以上。全高次数の係数。
使われ方：Goerss–Jardine VIII §1。塔の係数複体の正規化 cochain による表示。
-/

@[expose] public section
universe u
open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra.SkeletalCellAttachment

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 入出力の次数を同じ添字で読むための固定した係数群。 -/
abbrev positiveAdditiveCoefficient (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] (n r : ℕ) :=
  Additive (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup Y.right (n + 1 + (r + 1)) Y.basepoint)

/-- 実際の塔の係数微分を加法表示にし、出力の次数を入力の次数と同定する。 -/
def positiveAdditiveCoefficientDifferential (K : SSet.{u}) (Y : PointedSimplicialSet.{u})
    [KanComplex Y.right] (n r : ℕ) :
    (K.nonDegenerate (n + 1) → positiveAdditiveCoefficient Y n r) →+
      (K.nonDegenerate (n + 2) → positiveAdditiveCoefficient Y n r) where
  toFun a s := (coefficientIndexEquiv Y
    (by omega : n + 1 + 1 + r = n + 1 + (r + 1))).toAdditive
      (Additive.ofMul (coefficientDifferential K Y n r
        (fun t ↦ Additive.toMul (a t)) s))
  map_zero' := by
    funext s
    change (coefficientIndexEquiv Y _).toAdditive
      (Additive.ofMul (coefficientDifferential K Y n r 1 s)) = 0
    rw [map_one]
    exact map_zero _
  map_add' a b := by
    funext s
    change (coefficientIndexEquiv Y _).toAdditive
      (Additive.ofMul (coefficientDifferential K Y n r
        ((fun t ↦ Additive.toMul (a t)) * (fun t ↦ Additive.toMul (b t))) s)) = _
    rw [map_mul, Pi.mul_apply, ofMul_mul, map_add]
    rfl

/-- 加法表示に移した実際の係数微分は、通常の微分の指定した整数倍。 -/
theorem positiveAdditiveCoefficientDifferential_eq (K : SSet.{u}) (Y : PointedSimplicialSet.{u})
    [KanComplex Y.right] (n r : ℕ) :
    positiveAdditiveCoefficientDifferential K Y n r = (-1 : ℤ) ^ (n + 3 + r) •
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedValueCochains.differential K (AddCommGrpCat.of (positiveAdditiveCoefficient Y n r))
        (n + 1) := by
  ext a s
  exact coefficientDifferential_all_alternating K Y n r (fun t ↦ Additive.toMul (a t)) s

/-- 実際の塔の係数微分の核は、通常の正規化 cochain の cocycle 群。 -/
theorem positiveAdditiveCoefficientDifferential_ker (K : SSet.{u}) (Y : PointedSimplicialSet.{u})
    [KanComplex Y.right] (n r : ℕ) :
    (positiveAdditiveCoefficientDifferential K Y n r).ker =
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedValueCochains.differential K (AddCommGrpCat.of (positiveAdditiveCoefficient Y n r))
        (n + 1)).ker := by
  rw [positiveAdditiveCoefficientDifferential_eq]
  exact signed_ker _ _

/-- 実際の塔の係数微分の像は、通常の正規化 cochain の coboundary 群。 -/
theorem positiveAdditiveCoefficientDifferential_range (K : SSet.{u}) (Y : PointedSimplicialSet.{u})
    [KanComplex Y.right] (n r : ℕ) :
    (positiveAdditiveCoefficientDifferential K Y n r).range =
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedValueCochains.differential K (AddCommGrpCat.of (positiveAdditiveCoefficient Y n r))
        (n + 1)).range := by
  rw [positiveAdditiveCoefficientDifferential_eq]
  exact signed_range _ _


end
end SerrePositivity.KST.Spectra.SkeletalCellAttachment
