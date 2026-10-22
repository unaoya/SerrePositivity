module
public import SerrePositivity.InfinityCategories.Derived.Gluing.KernelShiftObject
public import SerrePositivity.InfinityCategories.Derived.Gluing.CommaStrictGradedElements
public import SerrePositivity.InfinityCategories.Derived.Gluing.NormalizedShiftSquare

/-! 標準 kernel シフトから元の対象への、閉次数 n の実 comma 射影。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits HomologicalComplex DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (X : DGGluingObject R C D M) (n : ℤ)
local notation "F" => Morita.kernelTensor R D C M
local notation "S" => dgGluingKernelShiftObject R C D M X n
local notation "T" => dgGluingKernelObject R C D M X
local notation "a" => normalizedModuleShiftOut R D n (representable R X.right)
local notation "b" => normalizedModuleShiftOut R C n (representable R X.left)

/-- 両側の正規化した標準射影を、第三成分零の同じ斉次 comma 元へ束ねる。 -/
def dgGluingKernelShiftProjection :
    (dgFunctorCommaHomComplex R (RightModule R D) (RightModule R C) F S T).X n :=
  dgGluingCommaStrictGradedElement R (RightModule R D) (RightModule R C) F S T n a b

lemma dgGluingKernelShiftProjection_source :
    (dgFunctorCommaSourceHomMap R (RightModule R D) (RightModule R C) F S T).f n
      (dgGluingKernelShiftProjection R C D M X n) = a :=
  dgGluingCommaStrictGradedElement_source R (RightModule R D) (RightModule R C)
    F S T n a b

lemma dgGluingKernelShiftProjection_replacement :
    (dgFunctorCommaReplacementHomMap R (RightModule R D) (RightModule R C) F S T).f n
      (dgGluingKernelShiftProjection R C D M X n) = b :=
  dgGluingCommaStrictGradedElement_replacement R (RightModule R D) (RightModule R C)
    F S T n a b

lemma dgGluingKernelShiftProjection_primitive :
    (dgFunctorCommaPrimitive R (RightModule R D) (RightModule R C) F S T).v
      n (n - 1) (by omega) (dgGluingKernelShiftProjection R C D M X n) = 0 :=
  dgGluingCommaStrictGradedElement_primitive R (RightModule R D) (RightModule R C)
    F S T n a b

/-- 同じ二射影は、シフトした augmentation の厳密正方形を満たす。 -/
lemma dgGluingKernelShiftProjection_square :
    (dgFunctorCommaDifference R (RightModule R D) (RightModule R C) F S T).f n
      (dgGluingBiproductElement _ _ n a b) = 0 := by
  simp only [dgFunctorCommaDifference, HomologicalComplex.sub_f_apply,
    ModuleCat.hom_sub, LinearMap.sub_apply, HomologicalComplex.comp_f,
    ModuleCat.comp_apply]
  erw [dgGluingBiproductElement_fst, dgGluingBiproductElement_snd]
  apply sub_eq_zero.mpr
  exact dgGluingNormalizedShiftSquare R D C F (representable R X.right)
    (representable R X.left) n (dgGluingKernelLift R C D M X)

/-- 任意整数次数の同じ実射影は閉じている。 -/
lemma dgGluingKernelShiftProjection_closed :
    (dgFunctorCommaHomComplex R (RightModule R D) (RightModule R C) F S T).d
      n (n + 1) (dgGluingKernelShiftProjection R C D M X n) = 0 := by
  exact dgGluingCommaStrictGradedElement_closed R (RightModule R D) (RightModule R C)
    F S T n a b (normalizedModuleShiftOut_d R D n (representable R X.right))
    (normalizedModuleShiftOut_d R C n (representable R X.left))
    (dgGluingKernelShiftProjection_square R C D M X n)

end SerrePositivity.InfinityCategories
