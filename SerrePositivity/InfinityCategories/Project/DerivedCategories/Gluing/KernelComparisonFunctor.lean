module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.KernelFunctor
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.KernelHomIdentity

/-! 対象と Hom 比較を直接指定した、同じ native/kernel dg 関手。 -/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)

/-- 同じ両代表対象と実 Hom 鎖同型を、その単位・合成保存により直接束ねた dg 関手。 -/
def dgGluingKernelComparisonFunctor :
    DGFunctor R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R (RightModule R D) (RightModule R C)
        (Morita.kernelTensor R D C M)) where
  obj := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelObject R C D M
  map X Y := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelHomIso R C D M X Y).hom
  map_id X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelHomIso_identity R C D M X
  map_comp X Y Z := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelHomIso_composition R C D M X Y Z

/-- 直接表示の対象も、既存の合成 dg 関手と同じ kernel 対象。 -/
lemma dgGluingKernelComparisonFunctor_obj (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    (dgGluingKernelComparisonFunctor R C D M).obj X =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToKernelComma R C D M).obj X := rfl

/-- 直接表示の実 Hom 写像も、既存の合成 dg 関手と同じ鎖写像。 -/
lemma dgGluingKernelComparisonFunctor_map (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    (dgGluingKernelComparisonFunctor R C D M).map X Y =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToKernelComma R C D M).map X Y :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToKernelComma_map R C D M X Y).symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
