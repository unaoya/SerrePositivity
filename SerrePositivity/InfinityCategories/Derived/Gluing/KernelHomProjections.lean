module
public import SerrePositivity.InfinityCategories.Derived.Gluing.KernelHomComparison

/-! kernel Hom 比較の同じ二射影と全整数次数の第三 cochain を回収する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits CochainComplex HomComplex DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (X Y : DGGluingObject R C D M)
local notation "F" => Morita.kernelTensor R D C M
local notation "B" => dgGluingKernelObject R C D M X
local notation "T" => dgGluingKernelObject R C D M Y

/-- 右成分は、元の右 Hom 射影を同じ D の Yoneda で送った写像。 -/
lemma dgGluingKernelHomIso_right :
    (dgGluingKernelHomIso R C D M X Y).hom ≫
      dgFunctorCommaSourceHomMap R (RightModule R D) (RightModule R C) F B T =
    dgGluingRightHomMap R C D M X Y ≫ yonedaHom R D X.right Y.right := by
  simp only [dgGluingKernelHomIso, complexMappingCoconeMapIso,
    dgFunctorCommaSourceHomMap, ← Category.assoc, complexMappingCoconeMap_fst]
  rw [Category.assoc, dgGluingKernelHomComponentsIso_hom]
  erw [biprod.lift_fst]
  simp only [dgGluingRightHomMap, Category.assoc]

/-- 左成分も、元の左 Hom 射影を同じ C の Yoneda で送った写像。 -/
lemma dgGluingKernelHomIso_left :
    (dgGluingKernelHomIso R C D M X Y).hom ≫
      dgFunctorCommaReplacementHomMap R (RightModule R D) (RightModule R C) F B T =
    dgGluingLeftHomMap R C D M X Y ≫ yonedaHom R C X.left Y.left := by
  simp only [dgGluingKernelHomIso, complexMappingCoconeMapIso,
    dgFunctorCommaReplacementHomMap, ← Category.assoc, complexMappingCoconeMap_fst]
  rw [Category.assoc, dgGluingKernelHomComponentsIso_hom]
  erw [biprod.lift_snd]
  simp only [dgGluingLeftHomMap, Category.assoc]

/-- 第三 cochain は、元の同じ第三 cochain を列同型で送ったもの。 -/
lemma dgGluingKernelHomIso_primitive :
    (Cochain.ofHom (dgGluingKernelHomIso R C D M X Y).hom).comp
      (dgFunctorCommaPrimitive R (RightModule R D) (RightModule R C) F B T)
      (zero_add (-1)) =
    (dgGluingHomPrimitive R C D M X Y).comp
      (Cochain.ofHom (dgGluingKernelHomTargetIso R C D M X Y).hom) (add_zero (-1)) := by
  simp only [dgGluingKernelHomIso, complexMappingCoconeMapIso,
    dgFunctorCommaPrimitive, dgGluingHomPrimitive]
  exact complexMappingCoconeMap_snd _ _ _ _ _

/-- 同じ第三 cochain の回収を、任意整数次数の二成分の等式で読む。 -/
lemma dgGluingKernelHomIso_primitive_v (p q : ℤ) (hpq : p + -1 = q) :
    (dgGluingKernelHomIso R C D M X Y).hom.f p ≫
      (dgFunctorCommaPrimitive R (RightModule R D) (RightModule R C) F B T).v p q hpq =
    (dgGluingHomPrimitive R C D M X Y).v p q hpq ≫
      (dgGluingKernelHomTargetIso R C D M X Y).hom.f q := by
  have he := Cochain.congr_v (dgGluingKernelHomIso_primitive R C D M X Y) p q hpq
  simpa only [Cochain.zero_cochain_comp_v, Cochain.comp_zero_cochain_v,
    Cochain.ofHom_v] using he

end SerrePositivity.InfinityCategories
