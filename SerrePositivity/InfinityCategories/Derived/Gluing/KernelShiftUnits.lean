module
public import SerrePositivity.InfinityCategories.Derived.Gluing.KernelShiftProjection
public import SerrePositivity.InfinityCategories.Derived.Gluing.KernelShiftInclusion
public import SerrePositivity.InfinityCategories.Derived.Gluing.CommaElementExt
public import SerrePositivity.InfinityCategories.Derived.Gluing.CommaGradedUnits
public import SerrePositivity.InfinityCategories.Derived.DGFunctorCommaProjections

/-! 標準 kernel シフトの閉斉次射影・包含は、通常順の両合成で実 comma 単位を回収する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (X : DGGluingObject R C D M) (n : ℤ)
local notation "F" => Morita.kernelTensor R D C M
local notation "S" => dgGluingKernelShiftObject R C D M X n
local notation "T" => dgGluingKernelObject R C D M X
local notation "p" => dgGluingKernelShiftProjection R C D M X n
local notation "i" => dgGluingKernelShiftInclusion R C D M X n
local notation "H" => dgFunctorCommaSource R (RightModule R D) (RightModule R C) F
local notation "J" => dgFunctorCommaReplacement R (RightModule R D) (RightModule R C) F

/-- 射影の後に包含すると、同じ標準シフト対象の実単位。 -/
lemma dgGluingKernelShiftOutIn :
    compose R (x := S) (y := T) (z := S) i p (add_neg_cancel n) =
      (unitElement R S).val := by
  apply dgGluingCommaElement_ext R (RightModule R D) (RightModule R C) F S S 0
  · change ((H).map S S).f 0 _ = ((H).map S S).f 0 _
    rw [dgGluingFunctor_map_compose, (H).map_unitElement R]
    change compose R
      ((dgFunctorCommaSourceHomMap R (RightModule R D) (RightModule R C) F T S).f (-n) i)
      ((dgFunctorCommaSourceHomMap R (RightModule R D) (RightModule R C) F S T).f n p)
      (add_neg_cancel n) = _
    rw [dgGluingKernelShiftInclusion_source, dgGluingKernelShiftProjection_source]
    exact dgGluingNormalizedShiftOutIn R D n (representable R X.right)
  · change ((J).map S S).f 0 _ = ((J).map S S).f 0 _
    rw [dgGluingFunctor_map_compose, (J).map_unitElement R]
    change compose R
      ((dgFunctorCommaReplacementHomMap R (RightModule R D) (RightModule R C) F T S).f (-n) i)
      ((dgFunctorCommaReplacementHomMap R (RightModule R D) (RightModule R C) F S T).f n p)
      (add_neg_cancel n) = _
    rw [dgGluingKernelShiftInclusion_replacement, dgGluingKernelShiftProjection_replacement]
    exact dgGluingNormalizedShiftOutIn R C n (representable R X.left)
  · rw [dgGluingCommaCompose_primitive_zero R (RightModule R D) (RightModule R C)
      F S T S i p (add_neg_cancel n) (dgGluingKernelShiftProjection_primitive R C D M X n)
      (dgGluingKernelShiftInclusion_primitive R C D M X n)]
    exact (dgGluingCommaUnit_primitive R (RightModule R D) (RightModule R C) F S).symm

/-- 包含の後に射影すると、元の同じ kernel 対象の実単位。 -/
lemma dgGluingKernelShiftInOut :
    compose R (x := T) (y := S) (z := T) p i (neg_add_cancel n) =
      (unitElement R T).val := by
  apply dgGluingCommaElement_ext R (RightModule R D) (RightModule R C) F T T 0
  · change ((H).map T T).f 0 _ = ((H).map T T).f 0 _
    rw [dgGluingFunctor_map_compose, (H).map_unitElement R]
    change compose R
      ((dgFunctorCommaSourceHomMap R (RightModule R D) (RightModule R C) F S T).f n p)
      ((dgFunctorCommaSourceHomMap R (RightModule R D) (RightModule R C) F T S).f (-n) i)
      (neg_add_cancel n) = _
    rw [dgGluingKernelShiftProjection_source, dgGluingKernelShiftInclusion_source]
    exact dgGluingNormalizedShiftInOut R D n (representable R X.right)
  · change ((J).map T T).f 0 _ = ((J).map T T).f 0 _
    rw [dgGluingFunctor_map_compose, (J).map_unitElement R]
    change compose R
      ((dgFunctorCommaReplacementHomMap R (RightModule R D) (RightModule R C) F S T).f n p)
      ((dgFunctorCommaReplacementHomMap R (RightModule R D) (RightModule R C) F T S).f (-n) i)
      (neg_add_cancel n) = _
    rw [dgGluingKernelShiftProjection_replacement, dgGluingKernelShiftInclusion_replacement]
    exact dgGluingNormalizedShiftInOut R C n (representable R X.left)
  · rw [dgGluingCommaCompose_primitive_zero R (RightModule R D) (RightModule R C)
      F T S T p i (neg_add_cancel n) (dgGluingKernelShiftInclusion_primitive R C D M X n)
      (dgGluingKernelShiftProjection_primitive R C D M X n)]
    exact (dgGluingCommaUnit_primitive R (RightModule R D) (RightModule R C) F T).symm

end SerrePositivity.InfinityCategories
