module
public import SerrePositivity.DifferentialGraded.Module.ShiftResolution
public import SerrePositivity.InfinityCategories.DGNerve.NestedCut
public import SerrePositivity.InfinityCategories.DGNerve.Residual

/-! # 斉次 Hom と標的シフトの閉次数零 Hom の比較

概要：次数 n の元を n シフトへの次数零元へ移し、斉次射影で逆変換する。
方針：shift の斉次包含・射影の両逆関係と通常順の Leibniz 則を使う。
規約：原始元の逆変換では符号 (-1)^n を保持する。使われ方：β3 の高次障害の零化。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 次数 n の Hom 元を、標的の n シフトへの次数零元へ移す。 -/
def dgModuleHomRightShift {M N : RightModule A D} (n : ℤ)
    (f : GradedHom A M N n) : GradedHom A M (shiftModule n N) 0 :=
  compose A (moduleShiftInElement A D n N) f (add_neg_cancel n)

/-- 右シフトと斉次射影の合成は元の斉次元を厳密に回収する。 -/
lemma dgModuleHomRightShift_inverse {M N : RightModule A D} (n : ℤ)
    (f : GradedHom A M N n) :
    compose A (moduleShiftOutElement A D n N) (dgModuleHomRightShift A D n f)
      (zero_add n) = f := by
  rw [dgModuleHomRightShift, compose_assoc_of_sum f
    (moduleShiftInElement A D n N) (moduleShiftOutElement A D n N)
    (add_neg_cancel n) (neg_add_cancel n) (zero_add n), moduleShiftInOut, unit_compose]

/-- 斉次閉元はシフトされた Hom の実際の次数零閉元になる。 -/
lemma dgModuleHomRightShift_closed {M N : RightModule A D} (n : ℤ)
    (f : GradedHom A M N n) (hf : differential A f = 0) :
    differential A (dgModuleHomRightShift A D n f) = 0 := by
  have hi : differential A (D := RightModule A D) (x := N) (y := shiftModule n N)
      (n := -n) (moduleShiftInElement A D n N) = 0 :=
    moduleShiftInElement_d A D n N
  rw [dgModuleHomRightShift, differential_compose, hi,
    zero_compose, hf, compose_zero, smul_zero, add_zero]

/-- シフトされた Hom の原始元を、正しい次数と符号を持つ元の原始元へ戻す。 -/
lemma dgModuleHomRightShift_primitive {M N : RightModule A D} (n k : ℤ)
    (hkn : k + 1 = n) (f : GradedHom A M N n)
    (h : GradedHom A M (shiftModule n N) (-1))
    (hh : (moduleHom A D M (shiftModule n N)).d (-1) 0 h =
      dgModuleHomRightShift A D n f) :
    (moduleHom A D M N).d k n
      (n.negOnePow • compose A (moduleShiftOutElement A D n N) h (by omega)) = f := by
  subst n
  change differential A ((k + 1).negOnePow •
    compose A (moduleShiftOutElement A D (k + 1) N) h (by omega)) = f
  have ho : differential A (D := RightModule A D) (x := shiftModule (k + 1) N)
      (y := N) (n := k + 1) (moduleShiftOutElement A D (k + 1) N) = 0 :=
    moduleShiftOutElement_d A D (k + 1) N
  rw [differential_units_smul, differential_compose, ho,
    zero_compose, zero_add]
  change (k + 1).negOnePow • (k + 1).negOnePow •
    compose A (moduleShiftOutElement A D (k + 1) N)
      ((moduleHom A D M (shiftModule (k + 1) N)).d (-1) 0 h) (zero_add (k + 1)) = f
  rw [hh, dgModuleHomRightShift_inverse, smul_smul,
    Int.units_mul_self, one_smul]

end SerrePositivity.InfinityCategories
