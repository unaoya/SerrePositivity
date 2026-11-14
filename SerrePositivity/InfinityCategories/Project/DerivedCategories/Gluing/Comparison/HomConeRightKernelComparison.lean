module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.HomComplexes.Evaluation.HomConeRightTensorEvaluation

/-! 元の右係数と、同じ Yoneda 円錐の通常 kernel tensor への全 Hom 作用の一致。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory CochainComplex HomComplex
open DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (X Y Z : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
  (f : ForgetEnrichment.of (Complex R) Y ⟶ ForgetEnrichment.of (Complex R) Z)
local notation "rf" => CategoryTheory.Functor.map
  (SerrePositivity.DifferentialGraded.DGFunctor.onClosed (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight R C D M)) f
local notation "yf" => CategoryTheory.Functor.map
  (SerrePositivity.DifferentialGraded.DGFunctor.onClosed (dgYoneda R D)) rf
local notation "K" => ForgetEnrichment.to (Complex R) (moduleCone R D yf)
local notation "F" => Morita.kernelTensor R D C M
local notation "r" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeRightArrow R C D M X Y Z f
local notation "A" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeRightTensorAction R C D M X Y Z f
local notation "E" => moduleEvaluation R C X.left

/-- 右係数を同じ tensor–Yoneda 円錐同型で移すと、元の右 Yoneda Hom の kernel 作用になる。 -/
lemma dgGluingHomConeRightCoefficient_kernel :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeRightCoefficient R C D M X Y Z f ≫
      (E).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelConeIso R C D M rf).hom =
    A ≫ (dgYonedaIso R X.left ((F).obj K)).hom := by
  apply HomologicalComplex.hom_ext
  intro n
  apply mappingCone.ext_from r (n + 1) n rfl
  · have ht := Cochain.congr_v
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeRightTensorAction_inl_eval R C D M X Y Z f) (n + 1) n (by omega)
    have hk := Cochain.congr_v (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelConeIso_inl_eval R C D M rf X.left)
      (n + 1) n (by omega)
    simp only [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v,
      Cochain.ofHom_v, HomologicalComplex.comp_f] at ht hk
    simp only [HomologicalComplex.comp_f, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeRightCoefficient_map,
      mappingCone.map, mappingCone.inl_v_desc_f_assoc, Cochain.zero_cochain_comp_v,
      Cochain.ofHom_v]
    erw [Category.assoc, hk]
    simp only [Category.assoc] at ht
    exact ht.symm
  · have ht := congrArg (fun a => a.f n)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeRightTensorAction_inr_eval R C D M X Y Z f)
    have hk := congrArg (fun a => (E).map a) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelConeIso_inr R C D M rf)
    simp only [CategoryTheory.Functor.map_comp, moduleConeInr_eval] at hk
    have hkn := congrArg (fun a => a.f n) hk
    simp only [HomologicalComplex.comp_f] at ht hkn
    simp only [HomologicalComplex.comp_f, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeRightCoefficient_map,
      mappingCone.map, mappingCone.inr_f_desc_f_assoc]
    erw [Category.assoc, hkn]
    exact ht.symm

/-- 双加群作用の円錐を、同じ右 Yoneda 円錐の tensor 像への全 Hom と同定する。 -/
def dgGluingHomConeRightTensorTargetIso :
    mappingCone (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeAction R C D M X Y Z f) ≅
      moduleHom R C (representable R X.left) ((F).obj K) :=
  (E).mapIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelConeIso R C D M rf) ≪≫
    (dgYonedaIso R X.left ((F).obj K)).symm

/-- 元の右係数は、同じ右 Yoneda 円錐への全 Hom の通常 kernel 作用に一致する。 -/
lemma dgGluingHomConeRightCoefficient_kernel_module :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeRightCoefficient R C D M X Y Z f ≫
      (dgGluingHomConeRightTensorTargetIso R C D M X Y Z f).hom =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeRightModuleIso R C D M X Y Z f).hom ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelHomAction R C D M X K := by
  change _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeRightCoefficient R C D M X Y Z f ≫
    ((E).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelConeIso R C D M rf).hom ≫
      (dgYonedaIso R X.left ((F).obj K)).inv) = _
  rw [← Category.assoc, dgGluingHomConeRightCoefficient_kernel, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
