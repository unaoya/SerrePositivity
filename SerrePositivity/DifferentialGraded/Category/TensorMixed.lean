module
public import SerrePositivity.DifferentialGraded.Category.TensorInclusions

/-! # tensor積dg圏の混合作用・因子分解 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory
variable (A : Type u) [CommRing A] {B : Type v} {C : Type w}
  [DGCategory A B] [DGCategory A C]

/-- 純粋斉次Homは第一因子、第二因子の包含の豊穣順合成。 -/
lemma dgTensor_first_then_second {x y : B} {c d : C} {p q n : ℤ}
    (f : GradedHom A x y p) (g : GradedHom A c d q) (hn : p + q = n) :
    forward A (D := DGTensorCategory A B C) (x := ((x, c) : DGTensorCategory A B C))
      (y := ((y, c) : DGTensorCategory A B C)) (z := ((y, d) : DGTensorCategory A B C))
      ((dgTensorFirstHom A B C c x y).f p f)
      ((dgTensorSecondHom A B C y c d).f q g) hn =
        dgTensorElement A (x := (x, c)) (y := (y, d)) f g hn := by
  rw [dgTensorFirstHom_apply, dgTensorSecondHom_apply]
  have h := dgTensor_forward_of_sum A (x := (x, c)) (y := (y, c)) (z := (y, d))
    f (unitElement A c).val (unitElement A y).val g
    (add_zero p) (zero_add q) (add_zero p) (zero_add q) hn
  simpa only [add_zero, zero_add, zero_mul, Int.negOnePow_zero, one_smul,
    unit_forward, forward_unit] using h

/-- 逆順では二つの因子の次数積の符号を得る。 -/
lemma dgTensor_second_then_first {x y : B} {c d : C} {p q n : ℤ}
    (f : GradedHom A x y p) (g : GradedHom A c d q) (hn : q + p = n) :
    forward A (D := DGTensorCategory A B C) (x := ((x, c) : DGTensorCategory A B C))
      (y := ((x, d) : DGTensorCategory A B C)) (z := ((y, d) : DGTensorCategory A B C))
      ((dgTensorSecondHom A B C x c d).f q g)
      ((dgTensorFirstHom A B C d x y).f p f) hn =
        (q * p).negOnePow • dgTensorElement A (x := (x, c)) (y := (y, d)) f g (by omega) := by
  rw [dgTensorSecondHom_apply, dgTensorFirstHom_apply]
  have h := dgTensor_forward_of_sum A (x := (x, c)) (y := (x, d)) (z := (y, d))
    (unitElement A x).val g f (unitElement A d).val
    (zero_add q) (add_zero p) (zero_add p) (add_zero q) hn
  simpa only [add_zero, zero_add, unit_forward, forward_unit] using h

end SerrePositivity.DifferentialGraded
