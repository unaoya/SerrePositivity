module

public import SerrePositivity.KST.Spectra.SkeletalCoefficientAlternating

/-!
概要：実際の係数微分を固定した加法的係数の cochain 準同型として表示する。
方針：出力の次数を標準同定し、各セルでの交代式を準同型の等式へ束ねる。
規約：cochain 次数二以上。任意の高次数係数。
使われ方：Goerss–Jardine VIII §1。核と像を通常の正規化 cochain と比較する。
-/

@[expose] public section
universe u
open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra.SkeletalCellAttachment

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 入出力の次数を同じ添字で読むための固定した係数群。 -/
abbrev additiveCoefficient (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] (n r : ℕ) :=
  Additive (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup Y.right (n + 2 + (r + 1)) Y.basepoint)

/-- 実際の塔の係数微分を加法表示にし、出力の次数を入力の次数と同定する。 -/
def additiveCoefficientDifferential (K : SSet.{u}) (Y : PointedSimplicialSet.{u})
    [KanComplex Y.right] (n r : ℕ) :
    (K.nonDegenerate (n + 2) → additiveCoefficient Y n r) →+
      (K.nonDegenerate (n + 3) → additiveCoefficient Y n r) where
  toFun a s := (coefficientIndexEquiv Y
    (by omega : n + 1 + 1 + 1 + r = n + 2 + (r + 1))).toAdditive
      (Additive.ofMul (coefficientDifferential K Y (n + 1) r
        (fun t ↦ Additive.toMul (a t)) s))
  map_zero' := by
    funext s
    change (coefficientIndexEquiv Y _).toAdditive
      (Additive.ofMul (coefficientDifferential K Y (n + 1) r 1 s)) = 0
    rw [map_one]
    exact map_zero _
  map_add' a b := by
    funext s
    change (coefficientIndexEquiv Y _).toAdditive
      (Additive.ofMul (coefficientDifferential K Y (n + 1) r
        ((fun t ↦ Additive.toMul (a t)) * (fun t ↦ Additive.toMul (b t))) s)) = _
    rw [map_mul, Pi.mul_apply, ofMul_mul, map_add]
    rfl

/-- 加法表示に移した実際の係数微分は、通常の微分の指定した整数倍。 -/
theorem additiveCoefficientDifferential_eq (K : SSet.{u}) (Y : PointedSimplicialSet.{u})
    [KanComplex Y.right] (n r : ℕ) :
    additiveCoefficientDifferential K Y n r = (-1 : ℤ) ^ (n + 4 + r) •
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedValueCochains.differential K (AddCommGrpCat.of (additiveCoefficient Y n r))
        (n + 2) := by
  ext a s
  exact coefficientDifferential_alternating K Y n r (fun t ↦ Additive.toMul (a t)) s

/-- 符号の整数倍は加法準同型の核を変えない。 -/
lemma signed_ker {A B : Type u} [AddCommGroup A] [AddCommGroup B]
    (f : A →+ B) (j : ℕ) : (((-1 : ℤ) ^ j) • f).ker = f.ker := by
  ext a
  change (((-1 : ℤ) ^ j) • f) a = 0 ↔ f a = 0
  rw [AddMonoidHom.zsmul_apply]
  rcases neg_one_pow_eq_or ℤ j with hs | hs <;> simp only [hs, one_zsmul,
    neg_one_zsmul, neg_eq_zero]

/-- 符号の整数倍は加法準同型の像を変えない。 -/
lemma signed_range {A B : Type u} [AddCommGroup A] [AddCommGroup B]
    (f : A →+ B) (j : ℕ) : (((-1 : ℤ) ^ j) • f).range = f.range := by
  ext b
  change (∃ a, (((-1 : ℤ) ^ j) • f) a = b) ↔ ∃ a, f a = b
  simp only [AddMonoidHom.zsmul_apply]
  rcases neg_one_pow_eq_or ℤ j with hs | hs
  · simp only [hs, one_zsmul]
  · simp only [hs, neg_one_zsmul]
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨-a, (map_neg f a).trans ha⟩
    · rintro ⟨a, ha⟩
      refine ⟨-a, ?_⟩
      rw [map_neg, neg_neg]
      exact ha

/-- 実際の塔の係数微分の核は、通常の正規化 cochain の cocycle 群。 -/
theorem additiveCoefficientDifferential_ker (K : SSet.{u}) (Y : PointedSimplicialSet.{u})
    [KanComplex Y.right] (n r : ℕ) :
    (additiveCoefficientDifferential K Y n r).ker =
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedValueCochains.differential K (AddCommGrpCat.of (additiveCoefficient Y n r))
        (n + 2)).ker := by
  rw [additiveCoefficientDifferential_eq]
  exact signed_ker _ _

/-- 実際の塔の係数微分の像は、通常の正規化 cochain の coboundary 群。 -/
theorem additiveCoefficientDifferential_range (K : SSet.{u}) (Y : PointedSimplicialSet.{u})
    [KanComplex Y.right] (n r : ℕ) :
    (additiveCoefficientDifferential K Y n r).range =
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedValueCochains.differential K (AddCommGrpCat.of (additiveCoefficient Y n r))
        (n + 2)).range := by
  rw [additiveCoefficientDifferential_eq]
  exact signed_range _ _

end
end SerrePositivity.KST.Spectra.SkeletalCellAttachment
