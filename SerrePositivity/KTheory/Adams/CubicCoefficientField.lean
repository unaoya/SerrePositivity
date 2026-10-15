module

public import Mathlib.NumberTheory.Cyclotomic.Basic

/-! # A characteristic-zero coefficient field with a cubic character root -/

@[expose] public section
noncomputable section
namespace SerrePositivity
namespace Adams

abbrev CubicCoefficientField := CyclotomicField 3 ℚ

local instance : IsCyclotomicExtension {3} ℚ CubicCoefficientField :=
  CyclotomicField.isCyclotomicExtension 3 ℚ

def cubicCoefficientRoot : CubicCoefficientField :=
  Classical.choose (IsCyclotomicExtension.exists_isPrimitiveRoot ℚ CubicCoefficientField
    (S := ({3} : Set ℕ)) (n := 3) (by simp) (by decide))

lemma cubicCoefficientRoot_primitive : IsPrimitiveRoot cubicCoefficientRoot 3 := by
  unfold cubicCoefficientRoot
  exact Classical.choose_spec (IsCyclotomicExtension.exists_isPrimitiveRoot ℚ CubicCoefficientField
    (S := ({3} : Set ℕ)) (n := 3) (by simp) (by decide))

lemma cubicCoefficientRoot_relation : cubicCoefficientRoot ^ 2 + cubicCoefficientRoot + 1 = 0 := by
  have hp := cubicCoefficientRoot_primitive.pow_eq_one
  have hn := cubicCoefficientRoot_primitive.ne_one (by decide)
  have he : (cubicCoefficientRoot - 1) *
      (cubicCoefficientRoot ^ 2 + cubicCoefficientRoot + 1) = 0 := by
    calc
      _ = cubicCoefficientRoot ^ 3 - 1 := by ring
      _ = 0 := by rw [hp, sub_self]
  exact (mul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr hn)

end Adams
end SerrePositivity
