module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.HomComplexes.Models.HomConeInclusion
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.Kernels.KernelHomFactorization
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.StableStructure.KernelConeInclusion

/-! 左右および係数の Hom 円錐同型は、元の加群円錐の右包含を回収する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory CochainComplex HomComplex DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (X Y Z : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
  (f : ForgetEnrichment.of (Complex R) Y ⟶ ForgetEnrichment.of (Complex R) Z)
local notation "P" => ForgetEnrichment.of (Complex R) (representable R X.left)
local notation "Q" => ForgetEnrichment.of (Complex R) (representable R X.right)
local notation "lf" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeLeftArrow R C D M Y Z f
local notation "rf" => CategoryTheory.Functor.map
  (DGFunctor.onClosed (dgYoneda R D)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeRightArrow R C D M Y Z f)

omit [Small.{u} D] in
/-- 左 Hom 円錐の右包含は、元の全 Yoneda Hom と左加群円錐の右包含の合成。 -/
lemma dgGluingHomConeLeftModuleIso_inr :
    mappingCone.inr (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeLeftArrow R C D M X Y Z f) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeLeftModuleIso R C D M X Y Z f).hom =
    yonedaHom R C X.left Z.left ≫ eHomWhiskerLeft (Complex R) P (moduleConeInr R C lf) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeLeftModuleIso, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeLeftSourceIso,
    Iso.trans_hom, Iso.symm_hom, ← Category.assoc]
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeInr_eqToIso _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftArrow_evaluate R C D M X Y Z f).symm]
  have he := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingYoneda_postcompose_inv R C X.left (moduleConeInr R C lf)
  rw [moduleConeInr_eval] at he
  exact he

/-- 右 Hom 円錐の右包含も、同じ全 Yoneda Hom と右加群円錐の右包含の合成。 -/
lemma dgGluingHomConeRightModuleIso_inr :
    mappingCone.inr (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeRightArrow R C D M X Y Z f) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeRightModuleIso R C D M X Y Z f).hom =
    yonedaHom R D X.right Z.right ≫ eHomWhiskerLeft (Complex R) Q (moduleConeInr R D rf) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingYonedaConeIso_inr R D X.right Y.right Z.right
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight R C D M).onClosed.map f)

/-- 係数円錐の右包含は、元の kernel 係数比較と同じ tensor 像の右包含の後合成。 -/
lemma dgGluingHomConeRightTensorTargetIso_inr :
    mappingCone.inr (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeAction R C D M X Y Z f) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeRightTensorTargetIso R C D M X Y Z f).hom =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelHomTargetIso R C D M X Z).hom ≫
      eHomWhiskerLeft (Complex R) P
        ((Morita.kernelTensor R D C M).onClosed.map (moduleConeInr R D rf)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeTarget_comparison, ← Category.assoc]
  have he := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingYoneda_postcompose_inv R C X.left
    (moduleConeInr R C (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaClosedSourceMap R C D M
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M Y) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M Z)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToComma R C D M).onClosed.map f)))
  rw [moduleConeInr_eval] at he
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeImageModuleIso, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeLeftTargetIso,
    Iso.trans_hom, Iso.symm_hom, ← Category.assoc]
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeInr_eqToIso _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightArrow_evaluate R C D M X Y Z f).symm]
  erw [he, Category.assoc, ← eHomWhiskerLeft_comp (Complex R) P
    (moduleConeInr R C (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaClosedSourceMap R C D M
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M Y) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M Z)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToComma R C D M).onClosed.map f)))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaKernelConeIso R C D M
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M Y) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M Z)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToComma R C D M).onClosed.map f)).hom,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaKernelConeIso_inr R C D M
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M Y) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M Z)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToComma R C D M).onClosed.map f),
    eHomWhiskerLeft_comp (Complex R) P
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelColumnIso R C D M (ForgetEnrichment.of (Complex R) Z.right)).inv
      ((Morita.kernelTensor R D C M).onClosed.map (moduleConeInr R D rf))]
  rw [← Category.assoc]
  erw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelHomTargetIso_factorization R C D M X Z]
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaKernelTargetIso_hom]
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
