module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.KernelShiftObject
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.CommaStrictGradedElements
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.NormalizedShiftSquare

/-! 標準 kernel シフトから元の対象への、閉次数 n の実 comma 射影。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits HomologicalComplex DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) (n : ℤ)
local notation "F" => Morita.kernelTensor R D C M
local notation "S" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelShiftObject R C D M X n
local notation "T" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelObject R C D M X
local notation "a" => normalizedModuleShiftOut R D n (representable R X.right)
local notation "b" => normalizedModuleShiftOut R C n (representable R X.left)

/-- 両側の正規化した標準射影を、第三成分零の同じ斉次 comma 元へ束ねる。 -/
def dgGluingKernelShiftProjection :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R (RightModule R D) (RightModule R C) F S T).X n :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaStrictGradedElement R (RightModule R D) (RightModule R C) F S T n a b

lemma dgGluingKernelShiftProjection_source :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSourceHomMap R (RightModule R D) (RightModule R C) F S T).f n
      (dgGluingKernelShiftProjection R C D M X n) = a :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaStrictGradedElement_source R (RightModule R D) (RightModule R C)
    F S T n a b

lemma dgGluingKernelShiftProjection_replacement :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacementHomMap R (RightModule R D) (RightModule R C) F S T).f n
      (dgGluingKernelShiftProjection R C D M X n) = b :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaStrictGradedElement_replacement R (RightModule R D) (RightModule R C)
    F S T n a b

lemma dgGluingKernelShiftProjection_primitive :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R (RightModule R D) (RightModule R C) F S T).v
      n (n - 1) (by omega) (dgGluingKernelShiftProjection R C D M X n) = 0 :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaStrictGradedElement_primitive R (RightModule R D) (RightModule R C)
    F S T n a b

/-- 同じ二射影は、シフトした augmentation の厳密正方形を満たす。 -/
lemma dgGluingKernelShiftProjection_square :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaDifference R (RightModule R D) (RightModule R C) F S T).f n
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingBiproductElement _ _ n a b) = 0 := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaDifference, HomologicalComplex.sub_f_apply,
    ModuleCat.hom_sub, LinearMap.sub_apply, HomologicalComplex.comp_f,
    ModuleCat.comp_apply]
  erw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingBiproductElement_fst, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingBiproductElement_snd]
  apply sub_eq_zero.mpr
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNormalizedShiftSquare R D C F (representable R X.right)
    (representable R X.left) n (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelLift R C D M X)

/-- 任意整数次数の同じ実射影は閉じている。 -/
lemma dgGluingKernelShiftProjection_closed :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R (RightModule R D) (RightModule R C) F S T).d
      n (n + 1) (dgGluingKernelShiftProjection R C D M X n) = 0 := by
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaStrictGradedElement_closed R (RightModule R D) (RightModule R C)
    F S T n a b (normalizedModuleShiftOut_d R D n (representable R X.right))
    (normalizedModuleShiftOut_d R C n (representable R X.left))
    (dgGluingKernelShiftProjection_square R C D M X n)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
