module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomConeRightKernelComparison
public import SerrePositivity.InfinityCategories.Derived.Gluing.ConeObjectTransport

/-! 左右 Hom 円錐の係数で使用した標的同型を揃える。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory CochainComplex HomComplex
open DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (X Y Z : DGGluingObject R C D M)
  (f : ForgetEnrichment.of (Complex R) Y ⟶ ForgetEnrichment.of (Complex R) Z)
local notation "B" => dgGluingCommaObject R C D M Y
local notation "C'" => dgGluingCommaObject R C D M Z
local notation "cf" => CategoryTheory.Functor.map
  (SerrePositivity.DifferentialGraded.DGFunctor.onClosed (dgGluingToComma R C D M)) f
local notation "k" => dgGluingCommaKernelConeIso R C D M B C' cf
local notation "T" => ForgetEnrichment.of (Complex R) (representable R X.left)

/-- 左係数の標的に同じ tensor 比較を続けると、右係数の標的同型と厳密に一致する。 -/
lemma dgGluingHomConeTarget_comparison :
    (dgGluingHomConeRightTensorTargetIso R C D M X Y Z f).hom =
    (dgGluingHomConeImageModuleIso R C D M X Y Z f).hom ≫
      eHomWhiskerLeft (Complex R) T (k).hom := by
  have hn := dgGluingYoneda_postcompose_inv R C X.left (k).hom
  simp only [dgGluingHomConeRightTensorTargetIso, dgGluingHomConeImageModuleIso,
    Iso.trans_hom, Iso.symm_hom, CategoryTheory.Functor.mapIso_hom]
  erw [Category.assoc, ← hn]
  simp only [dgGluingCommaKernelConeIso, Iso.trans_hom, eqToIso.hom,
    eqToHom_refl, Category.id_comp]
  rfl

/-- 左係数も同じ tensor 標的に移すと、元の cone 比較と tensor 比較の合成の後合成になる。 -/
lemma dgGluingHomConeLeftCoefficient_kernel_module :
    dgGluingHomConeLeftCoefficient R C D M X Y Z f ≫
      (dgGluingHomConeRightTensorTargetIso R C D M X Y Z f).hom =
    -((dgGluingHomConeLeftModuleIso R C D M X Y Z f).hom ≫
      eHomWhiskerLeft (Complex R) T (dgGluingConeMorphism R C D M Y Z f ≫ (k).hom)) := by
  rw [dgGluingHomConeTarget_comparison, ← Category.assoc,
    dgGluingHomConeLeftCoefficient_module, Preadditive.neg_comp, Category.assoc]
  erw [← eHomWhiskerLeft_comp (Complex R) T (dgGluingConeMorphism R C D M Y Z f) (k).hom]

end SerrePositivity.InfinityCategories
