module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ContractingElementNerve
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Algebra

/-! # 収縮対象に接する Hom の閉元の原始元

概要：収縮対象へ入る、または出る全次数の閉元を明示的な境界として表す。
方針：収縮元との合成に Leibniz 則を適用し、始点側では次数による符号を掛ける。
規約：閉元の次数 n+1 と原始元の次数 n を固定する。使われ方：β3 の mapping space の収縮。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable {A : Type u} [CommRing A] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] {x y : D}

/-- 終点の収縮元から作る、入ってくる閉元の原始元。 -/
def contractingTargetPrimitive (h : _root_.SerrePositivity.DifferentialGraded.GradedHom A y y (-1)) (n : ℤ)
    (f : _root_.SerrePositivity.DifferentialGraded.GradedHom A x y (n + 1)) : GradedHom A x y n :=
  _root_.SerrePositivity.DifferentialGraded.compose A h f (by omega)

/-- 終点の収縮元で閉元を合成すれば、その微分は元の閉元。 -/
lemma contractingTargetPrimitive_differential (h : _root_.SerrePositivity.DifferentialGraded.GradedHom A y y (-1))
    (dh : (_root_.SerrePositivity.DifferentialGraded.homObject A D y y).d (-1) 0 h = (_root_.SerrePositivity.DifferentialGraded.unitElement A y).val)
    (n : ℤ) (f : _root_.SerrePositivity.DifferentialGraded.GradedHom A x y (n + 1)) (df : _root_.SerrePositivity.DifferentialGraded.differential A f = 0) :
    _root_.SerrePositivity.DifferentialGraded.differential A (contractingTargetPrimitive h n f) = f := by
  have dh' : _root_.SerrePositivity.DifferentialGraded.differential A h = (_root_.SerrePositivity.DifferentialGraded.unitElement A y).val := dh
  rw [contractingTargetPrimitive, _root_.SerrePositivity.DifferentialGraded.differential_compose, dh', df, _root_.SerrePositivity.DifferentialGraded.unit_compose,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_zero, smul_zero, add_zero]

/-- 始点の収縮元から作る、出ていく閉元の符号付き原始元。 -/
def contractingSourcePrimitive (h : _root_.SerrePositivity.DifferentialGraded.GradedHom A x x (-1)) (n : ℤ)
    (f : _root_.SerrePositivity.DifferentialGraded.GradedHom A x y (n + 1)) : GradedHom A x y n :=
  (n + 1).negOnePow • _root_.SerrePositivity.DifferentialGraded.compose A f h (by omega)

/-- 始点側では閉元の次数による符号を掛けると、その微分は元の閉元。 -/
lemma contractingSourcePrimitive_differential (h : _root_.SerrePositivity.DifferentialGraded.GradedHom A x x (-1))
    (dh : (_root_.SerrePositivity.DifferentialGraded.homObject A D x x).d (-1) 0 h = (_root_.SerrePositivity.DifferentialGraded.unitElement A x).val)
    (n : ℤ) (f : _root_.SerrePositivity.DifferentialGraded.GradedHom A x y (n + 1)) (df : _root_.SerrePositivity.DifferentialGraded.differential A f = 0) :
    _root_.SerrePositivity.DifferentialGraded.differential A (contractingSourcePrimitive h n f) = f := by
  have dh' : _root_.SerrePositivity.DifferentialGraded.differential A h = (_root_.SerrePositivity.DifferentialGraded.unitElement A x).val := dh
  change (_root_.SerrePositivity.DifferentialGraded.homObject A D x y).d n (n + 1)
    ((n + 1).negOnePow • _root_.SerrePositivity.DifferentialGraded.compose A f h (by omega)) = f
  simp only [Units.smul_def, map_zsmul]
  change (n + 1).negOnePow • _root_.SerrePositivity.DifferentialGraded.differential A (_root_.SerrePositivity.DifferentialGraded.compose A f h (by omega)) = f
  rw [differential_compose, df, dh', _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zero_compose, zero_add, compose_unit]
  simp only [smul_smul, Int.units_mul_self, one_smul]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
