module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleHomRightShift

/-! # シフトされた次数零 Hom の斉次元への逆変換

概要：シフトへの任意の次数零元を斉次射影で戻し、右 shift との両逆を証明する。
方針：shift の斉次単位の両逆関係と Leibniz 則を使う。
規約：元と cycle を厳密に回収する。使われ方：全次数の roof の閉加群分子を元へ戻す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]

/-- 標的の n shift への次数零元を元の次数 n の元へ戻す。 -/
def dgModuleHomRightUnshift {M N : _root_.SerrePositivity.DifferentialGraded.RightModule A D} (n : ℤ)
    (f : _root_.SerrePositivity.DifferentialGraded.GradedHom A M (shiftModule n N) 0) : _root_.SerrePositivity.DifferentialGraded.GradedHom A M N n :=
  _root_.SerrePositivity.DifferentialGraded.compose A (moduleShiftOutElement A D n N) f (zero_add n)

/-- 逆変換して右 shift すると、元の次数零元を厳密に回収する。 -/
lemma dgModuleHomRightShift_unshift {M N : _root_.SerrePositivity.DifferentialGraded.RightModule A D} (n : ℤ)
    (f : _root_.SerrePositivity.DifferentialGraded.GradedHom A M (shiftModule n N) 0) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHomRightShift A D n (dgModuleHomRightUnshift A D n f) = f := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHomRightShift, dgModuleHomRightUnshift,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NestedCut.compose_assoc_of_sum f (moduleShiftOutElement A D n N) (moduleShiftInElement A D n N)
      (zero_add n) (add_neg_cancel n) (add_neg_cancel n), moduleShiftOutIn, unit_compose]

/-- シフト Hom の次数零閉元は、逆変換後も閉元となる。 -/
lemma dgModuleHomRightUnshift_closed {M N : _root_.SerrePositivity.DifferentialGraded.RightModule A D} (n : ℤ)
    (f : _root_.SerrePositivity.DifferentialGraded.GradedHom A M (shiftModule n N) 0) (hf : _root_.SerrePositivity.DifferentialGraded.differential A f = 0) :
    _root_.SerrePositivity.DifferentialGraded.differential A (dgModuleHomRightUnshift A D n f) = 0 := by
  have ho : _root_.SerrePositivity.DifferentialGraded.differential A (D := RightModule A D) (x := shiftModule n N) (y := N)
      (n := n) (moduleShiftOutElement A D n N) = 0 := _root_.SerrePositivity.DifferentialGraded.moduleShiftOutElement_d A D n N
  rw [dgModuleHomRightUnshift, differential_compose, ho, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zero_compose, hf,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_zero, smul_zero, add_zero]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
