module
public import SerrePositivity.InfinityCategories.Derived.Gluing.KernelFunctor
public import SerrePositivity.InfinityCategories.Derived.Gluing.KernelHomIdentity

/-! 対象と Hom 比較を直接指定した、同じ native/kernel dg 関手。 -/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)

/-- 同じ両代表対象と実 Hom 鎖同型を、その単位・合成保存により直接束ねた dg 関手。 -/
def dgGluingKernelComparisonFunctor :
    DGFunctor R (DGGluingObject R C D M)
      (DGFunctorCommaObject R (RightModule R D) (RightModule R C)
        (Morita.kernelTensor R D C M)) where
  obj := dgGluingKernelObject R C D M
  map X Y := (dgGluingKernelHomIso R C D M X Y).hom
  map_id X := dgGluingKernelHomIso_identity R C D M X
  map_comp X Y Z := dgGluingKernelHomIso_composition R C D M X Y Z

/-- 直接表示の対象も、既存の合成 dg 関手と同じ kernel 対象。 -/
lemma dgGluingKernelComparisonFunctor_obj (X : DGGluingObject R C D M) :
    (dgGluingKernelComparisonFunctor R C D M).obj X =
      (dgGluingToKernelComma R C D M).obj X := rfl

/-- 直接表示の実 Hom 写像も、既存の合成 dg 関手と同じ鎖写像。 -/
lemma dgGluingKernelComparisonFunctor_map (X Y : DGGluingObject R C D M) :
    (dgGluingKernelComparisonFunctor R C D M).map X Y =
      (dgGluingToKernelComma R C D M).map X Y :=
  (dgGluingToKernelComma_map R C D M X Y).symm

end SerrePositivity.InfinityCategories
