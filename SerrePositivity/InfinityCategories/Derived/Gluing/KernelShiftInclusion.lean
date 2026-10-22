module
public import SerrePositivity.InfinityCategories.Derived.Gluing.KernelShiftObject
public import SerrePositivity.InfinityCategories.Derived.Gluing.CommaStrictGradedElements
public import SerrePositivity.InfinityCategories.Derived.Gluing.NormalizedShiftInverseSquare

/-! 元の対象から標準 kernel シフトへの、閉次数 −n の実 comma 包含。 -/
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
local notation "a" => dgGluingNormalizedShiftIn R D n (representable R X.right)
local notation "b" => dgGluingNormalizedShiftIn R C n (representable R X.left)

/-- 両側の正規化した標準包含を、第三成分零の同じ斉次 comma 元へ束ねる。 -/
def dgGluingKernelShiftInclusion :
    (dgFunctorCommaHomComplex R (RightModule R D) (RightModule R C) F T S).X (-n) :=
  dgGluingCommaStrictGradedElement R (RightModule R D) (RightModule R C) F T S (-n) a b

lemma dgGluingKernelShiftInclusion_source :
    (dgFunctorCommaSourceHomMap R (RightModule R D) (RightModule R C) F T S).f (-n)
      (dgGluingKernelShiftInclusion R C D M X n) = a :=
  dgGluingCommaStrictGradedElement_source R (RightModule R D) (RightModule R C)
    F T S (-n) a b

lemma dgGluingKernelShiftInclusion_replacement :
    (dgFunctorCommaReplacementHomMap R (RightModule R D) (RightModule R C) F T S).f (-n)
      (dgGluingKernelShiftInclusion R C D M X n) = b :=
  dgGluingCommaStrictGradedElement_replacement R (RightModule R D) (RightModule R C)
    F T S (-n) a b

lemma dgGluingKernelShiftInclusion_primitive :
    (dgFunctorCommaPrimitive R (RightModule R D) (RightModule R C) F T S).v
      (-n) (-n - 1) (by omega) (dgGluingKernelShiftInclusion R C D M X n) = 0 :=
  dgGluingCommaStrictGradedElement_primitive R (RightModule R D) (RightModule R C)
    F T S (-n) a b

/-- 同じ二包含は、シフトした augmentation の厳密正方形を満たす。 -/
lemma dgGluingKernelShiftInclusion_square :
    (dgFunctorCommaDifference R (RightModule R D) (RightModule R C) F T S).f (-n)
      (dgGluingBiproductElement _ _ (-n) a b) = 0 := by
  simp only [dgFunctorCommaDifference, HomologicalComplex.sub_f_apply,
    ModuleCat.hom_sub, LinearMap.sub_apply, HomologicalComplex.comp_f,
    ModuleCat.comp_apply]
  erw [dgGluingBiproductElement_fst, dgGluingBiproductElement_snd]
  apply sub_eq_zero.mpr
  exact dgGluingNormalizedShiftInverseSquare R D C F (representable R X.right)
    (representable R X.left) n (dgGluingKernelLift R C D M X)

/-- 任意整数次数の同じ実包含は閉じている。 -/
lemma dgGluingKernelShiftInclusion_closed :
    (dgFunctorCommaHomComplex R (RightModule R D) (RightModule R C) F T S).d
      (-n) (-n + 1) (dgGluingKernelShiftInclusion R C D M X n) = 0 := by
  exact dgGluingCommaStrictGradedElement_closed R (RightModule R D) (RightModule R C)
    F T S (-n) a b (dgGluingNormalizedShiftIn_closed R D n (representable R X.right))
    (dgGluingNormalizedShiftIn_closed R C n (representable R X.left))
    (dgGluingKernelShiftInclusion_square R C D M X n)

end SerrePositivity.InfinityCategories
