module
public import SerrePositivity.InfinityCategories.Derived.Gluing.KernelHomFactorization

/-! 元の dg gluing から通常 kernel の加群 comma への実 dg 関手と、その同じ Hom 比較。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded MonoidalCategory
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)

/-- 元の二代表加群と augmentation の kernel 持ち上げを持つ実 dg 関手。 -/
def dgGluingToKernelComma :
    DGFunctor R (DGGluingObject R C D M)
      (DGFunctorCommaObject R (RightModule R D) (RightModule R C)
        (Morita.kernelTensor R D C M)) :=
  (dgGluingToComma R C D M).comp (dgGluingCommaToKernel R C D M)

/-- 同じ実 dg 関手の対象は、構成済みの native gluing の kernel 表示。 -/
lemma dgGluingToKernelComma_obj (X : DGGluingObject R C D M) :
    (dgGluingToKernelComma R C D M).obj X = dgGluingKernelObject R C D M X := rfl

/-- 実 dg 関手の全 Hom 写像は、構成済みの同じ native/kernel 鎖同型。 -/
lemma dgGluingToKernelComma_map (X Y : DGGluingObject R C D M) :
    (dgGluingToKernelComma R C D M).map X Y =
      (dgGluingKernelHomIso R C D M X Y).hom :=
  dgGluingKernelHomIso_factorization R C D M X Y

/-- native/kernel Hom 比較は、第三 cochain ごと全整数次数の実合成を保存する。 -/
lemma dgGluingKernelHomIso_composition (X Y Z : DGGluingObject R C D M) :
    dgGluingComposition R C D M X Y Z ≫ (dgGluingKernelHomIso R C D M X Z).hom =
    ((dgGluingKernelHomIso R C D M X Y).hom ⊗ₘ
      (dgGluingKernelHomIso R C D M Y Z).hom) ≫
      dgFunctorCommaComposition R (RightModule R D) (RightModule R C)
        (Morita.kernelTensor R D C M) (dgGluingKernelObject R C D M X)
        (dgGluingKernelObject R C D M Y) (dgGluingKernelObject R C D M Z) := by
  have hc := (dgGluingToKernelComma R C D M).map_comp X Y Z
  simpa only [dgGluingToKernelComma_map] using! hc

end SerrePositivity.InfinityCategories
