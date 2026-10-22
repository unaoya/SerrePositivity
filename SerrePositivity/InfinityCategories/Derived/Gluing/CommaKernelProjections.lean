module
public import SerrePositivity.InfinityCategories.Derived.Gluing.CommaKernelComparison

/-! 加群 comma 比較の二射影と、全次数の第三 cochain。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded CochainComplex HomComplex
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (X Y : DGFunctorCommaObject R D (RightModule R C) M.toFunctor)
local notation "F" => Morita.kernelTensor R D C M
local notation "B" => dgGluingCommaKernelObject R C D M X
local notation "T" => dgGluingCommaKernelObject R C D M Y

/-- 右射影は、元の同じ射影を D の全 Yoneda Hom で送ったもの。 -/
lemma dgGluingCommaKernelHomIso_source :
    (dgGluingCommaKernelHomIso R C D M X Y).hom ≫
      dgFunctorCommaSourceHomMap R (RightModule R D) (RightModule R C) F B T =
    dgFunctorCommaSourceHomMap R D (RightModule R C) M.toFunctor X Y ≫
      yonedaHom R D X.source Y.source := by
  simp only [dgGluingCommaKernelHomIso, complexMappingCoconeMapIso,
    dgFunctorCommaSourceHomMap, ← Category.assoc, complexMappingCoconeMap_fst]
  rw [Category.assoc, biprod.mapIso_hom]
  erw [biprod.map_fst]
  rfl

/-- 左射影は、元の同じ射影をそのまま回収する。 -/
lemma dgGluingCommaKernelHomIso_replacement :
    (dgGluingCommaKernelHomIso R C D M X Y).hom ≫
      dgFunctorCommaReplacementHomMap R (RightModule R D) (RightModule R C) F B T =
    dgFunctorCommaReplacementHomMap R D (RightModule R C) M.toFunctor X Y := by
  simp only [dgGluingCommaKernelHomIso, complexMappingCoconeMapIso,
    dgFunctorCommaReplacementHomMap, ← Category.assoc, complexMappingCoconeMap_fst]
  rw [Category.assoc, biprod.mapIso_hom]
  erw [biprod.map_snd]
  simp only [Iso.refl_hom, Category.comp_id]

/-- 第三 cochain は、元の同じ第三 cochain の係数列同型による像。 -/
lemma dgGluingCommaKernelHomIso_primitive :
    (Cochain.ofHom (dgGluingCommaKernelHomIso R C D M X Y).hom).comp
      (dgFunctorCommaPrimitive R (RightModule R D) (RightModule R C) F B T)
      (zero_add (-1)) =
    (dgFunctorCommaPrimitive R D (RightModule R C) M.toFunctor X Y).comp
      (Cochain.ofHom (dgGluingCommaKernelTargetIso R C D M X Y).hom) (add_zero (-1)) := by
  simp only [dgGluingCommaKernelHomIso, complexMappingCoconeMapIso, dgFunctorCommaPrimitive]
  exact complexMappingCoconeMap_snd _ _ _ _ _

end SerrePositivity.InfinityCategories
