module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomConeInclusion
public import SerrePositivity.InfinityCategories.Derived.Gluing.KernelHomFactorization
public import SerrePositivity.InfinityCategories.Derived.Gluing.KernelConeInclusion

/-! 左右および係数の Hom 円錐同型は、元の加群円錐の右包含を回収する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory CochainComplex HomComplex DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (X Y Z : DGGluingObject R C D M)
  (f : ForgetEnrichment.of (Complex R) Y ⟶ ForgetEnrichment.of (Complex R) Z)
local notation "P" => ForgetEnrichment.of (Complex R) (representable R X.left)
local notation "Q" => ForgetEnrichment.of (Complex R) (representable R X.right)
local notation "lf" => dgGluingConeLeftArrow R C D M Y Z f
local notation "rf" => CategoryTheory.Functor.map
  (DGFunctor.onClosed (dgYoneda R D)) (dgGluingConeRightArrow R C D M Y Z f)

omit [Small.{u} D] in
/-- 左 Hom 円錐の右包含は、元の全 Yoneda Hom と左加群円錐の右包含の合成。 -/
lemma dgGluingHomConeLeftModuleIso_inr :
    mappingCone.inr (dgGluingHomConeLeftArrow R C D M X Y Z f) ≫
      (dgGluingHomConeLeftModuleIso R C D M X Y Z f).hom =
    yonedaHom R C X.left Z.left ≫ eHomWhiskerLeft (Complex R) P (moduleConeInr R C lf) := by
  simp only [dgGluingHomConeLeftModuleIso, dgGluingHomConeLeftSourceIso,
    Iso.trans_hom, Iso.symm_hom, ← Category.assoc]
  rw [dgGluingConeInr_eqToIso _ _ (dgGluingLeftArrow_evaluate R C D M X Y Z f).symm]
  have he := dgGluingYoneda_postcompose_inv R C X.left (moduleConeInr R C lf)
  rw [moduleConeInr_eval] at he
  exact he

/-- 右 Hom 円錐の右包含も、同じ全 Yoneda Hom と右加群円錐の右包含の合成。 -/
lemma dgGluingHomConeRightModuleIso_inr :
    mappingCone.inr (dgGluingHomConeRightArrow R C D M X Y Z f) ≫
      (dgGluingHomConeRightModuleIso R C D M X Y Z f).hom =
    yonedaHom R D X.right Z.right ≫ eHomWhiskerLeft (Complex R) Q (moduleConeInr R D rf) :=
  dgGluingYonedaConeIso_inr R D X.right Y.right Z.right
    ((dgGluingRight R C D M).onClosed.map f)

/-- 係数円錐の右包含は、元の kernel 係数比較と同じ tensor 像の右包含の後合成。 -/
lemma dgGluingHomConeRightTensorTargetIso_inr :
    mappingCone.inr (dgGluingHomConeAction R C D M X Y Z f) ≫
      (dgGluingHomConeRightTensorTargetIso R C D M X Y Z f).hom =
    (dgGluingKernelHomTargetIso R C D M X Z).hom ≫
      eHomWhiskerLeft (Complex R) P
        ((Morita.kernelTensor R D C M).onClosed.map (moduleConeInr R D rf)) := by
  rw [dgGluingHomConeTarget_comparison, ← Category.assoc]
  have he := dgGluingYoneda_postcompose_inv R C X.left
    (moduleConeInr R C (dgGluingCommaClosedSourceMap R C D M
      (dgGluingCommaObject R C D M Y) (dgGluingCommaObject R C D M Z)
      ((dgGluingToComma R C D M).onClosed.map f)))
  rw [moduleConeInr_eval] at he
  simp only [dgGluingHomConeImageModuleIso, dgGluingHomConeLeftTargetIso,
    Iso.trans_hom, Iso.symm_hom, ← Category.assoc]
  rw [dgGluingConeInr_eqToIso _ _ (dgGluingRightArrow_evaluate R C D M X Y Z f).symm]
  erw [he, Category.assoc, ← eHomWhiskerLeft_comp (Complex R) P
    (moduleConeInr R C (dgGluingCommaClosedSourceMap R C D M
      (dgGluingCommaObject R C D M Y) (dgGluingCommaObject R C D M Z)
      ((dgGluingToComma R C D M).onClosed.map f)))
    (dgGluingCommaKernelConeIso R C D M
      (dgGluingCommaObject R C D M Y) (dgGluingCommaObject R C D M Z)
      ((dgGluingToComma R C D M).onClosed.map f)).hom,
    dgGluingCommaKernelConeIso_inr R C D M
      (dgGluingCommaObject R C D M Y) (dgGluingCommaObject R C D M Z)
      ((dgGluingToComma R C D M).onClosed.map f),
    eHomWhiskerLeft_comp (Complex R) P
      (dgGluingKernelColumnIso R C D M (ForgetEnrichment.of (Complex R) Z.right)).inv
      ((Morita.kernelTensor R D C M).onClosed.map (moduleConeInr R D rf))]
  rw [← Category.assoc]
  erw [← dgGluingKernelHomTargetIso_factorization R C D M X Z]
  rw [dgGluingCommaKernelTargetIso_hom]
  rfl

end SerrePositivity.InfinityCategories
