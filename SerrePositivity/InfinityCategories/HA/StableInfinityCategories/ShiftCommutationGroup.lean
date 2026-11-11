module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ShiftCommutationInverse
public import Mathlib.Algebra.Group.Int.Defs

/-! # 全次数のシフト交換同型の群

概要：次数付きの交換同型のモノイドには全ての元の逆元がある。
方針：反対次数の交換同型が右逆元であることから、左逆元も導く。
規約：整数冪の次数は次数の整数倍。使われ方：一回の比較の整合的な整数への延長。
-/
@[expose] public section
noncomputable section
universe v u v' u'
open CategoryTheory
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  [HasShift C ℤ] [HasShift D ℤ] (F : C ⥤ D)

/-- 概要：全次数の交換同型の反対次数の元。
方針：次数の符号を反転し、シフトの単位・余単位で逆比較を作る。
規約：依存和の元として構成。使われ方：群の逆元。 -/
def stableShiftCommutationInverse (e : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableShiftCommutation F) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableShiftCommutation F :=
  ⟨-e.1, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableShiftCommutationNeg e.2⟩

/-- 概要：反対次数の元は右逆元。
方針：零次数への比較の計算を依存和へ移す。
規約：次数の和も同時に零へ移す。使われ方：逆元公理。 -/
lemma stableShiftCommutation_mul_inverse (e : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableShiftCommutation F) :
    e * stableShiftCommutationInverse F e = 1 := by
  apply Sigma.ext (add_neg_cancel e.1)
  exact (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableShiftCommutationIsoAdd_heq F (add_neg_cancel e.1) _ _).trans
    (heq_of_eq (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableShiftCommutation_mul_neg e.2))

/-- 概要：反対次数の元は左逆元でもある。
方針：全ての元の右逆元が存在するモノイドでは、右逆元の右逆元が元に一致する。
規約：既存のモノイドの結合則のみを使う。使われ方：群構造。 -/
lemma stableShiftCommutation_inverse_mul (e : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableShiftCommutation F) :
    stableShiftCommutationInverse F e * e = 1 := by
  let y := stableShiftCommutationInverse F e
  let z := stableShiftCommutationInverse F y
  have hy : e * y = 1 := stableShiftCommutation_mul_inverse F e
  have hz : y * z = 1 := stableShiftCommutation_mul_inverse F y
  have he : e = z := by
    calc
      e = e * 1 := (mul_one e).symm
      _ = e * (y * z) := by rw [hz]
      _ = (e * y) * z := (mul_assoc _ _ _).symm
      _ = z := by rw [hy, one_mul]
  change y * e = 1
  rw [he]
  exact hz

/-- 概要：全次数のシフト交換同型は群をなす。
方針：既存のモノイドに反対次数の逆元を加える。
規約：既存の乗法・単位を変更しない。使われ方：一回の交換同型の整数冪。 -/
instance stableShiftCommutation_group : Group (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableShiftCommutation F) where
  __ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableShiftCommutation_monoid F
  inv := stableShiftCommutationInverse F
  inv_mul_cancel := stableShiftCommutation_inverse_mul F

/-- 概要：交換同型の整数冪の次数は元の次数の整数倍。
方針：次数準同型は整数冪を保つ。
規約：加法表示に戻して記述する。使われ方：次数一から次数 n の比較を取り出す。 -/
lemma stableShiftCommutation_zpow_degree (e : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableShiftCommutation F) (n : ℤ) :
    (e ^ n).1 = n * e.1 := by
  have h := map_zpow (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableShiftCommutationDegree F) e n
  exact congrArg Multiplicative.toAdd h

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
