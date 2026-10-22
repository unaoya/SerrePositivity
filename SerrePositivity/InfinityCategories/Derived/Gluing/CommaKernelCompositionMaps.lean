module
public import SerrePositivity.InfinityCategories.Derived.Gluing.CommaKernelProjections
public import SerrePositivity.InfinityCategories.Derived.Gluing.TensorPrimitiveTransport

/-! kernel comma 比較は、全 Hom tensor 上の二つの primitive の係数合成を保つ。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded MonoidalCategory CochainComplex HomComplex
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (X Y Z : DGFunctorCommaObject R D (RightModule R C) M.toFunctor)
local notation "F" => Morita.kernelTensor R D C M
local notation "KX" => dgGluingCommaKernelObject R C D M X
local notation "KY" => dgGluingCommaKernelObject R C D M Y
local notation "KZ" => dgGluingCommaKernelObject R C D M Z
local notation "aXY" => Iso.hom (dgGluingCommaKernelHomIso R C D M X Y)
local notation "aYZ" => Iso.hom (dgGluingCommaKernelHomIso R C D M Y Z)
local notation "aXZ" => Iso.hom (dgGluingCommaKernelHomIso R C D M X Z)
local notation "cXY" => Iso.hom (dgGluingCommaKernelTargetIso R C D M X Y)
local notation "cYZ" => Iso.hom (dgGluingCommaKernelTargetIso R C D M Y Z)
local notation "cXZ" => Iso.hom (dgGluingCommaKernelTargetIso R C D M X Z)

/-- 第一 primitive の係数合成の可換性は、列比較の全 Hom 自然性による。 -/
lemma dgGluingCommaKernelFirstCompositionMap :
    (cXY ⊗ₘ aYZ) ≫
      dgFunctorCommaFirstCompositionMap R (RightModule R D) (RightModule R C)
        F KX KY KZ =
    dgFunctorCommaFirstCompositionMap R D (RightModule R C) M.toFunctor X Y Z ≫ cXZ := by
  simp only [dgFunctorCommaFirstCompositionMap, dgFunctorCommaImageHomMap,
    ← Category.assoc, tensorHom_comp_tensorHom]
  simp only [Category.assoc, dgGluingCommaKernelHomIso_source]
  have he := dgGluingKernelColumnIso_inv_composition R C D M
    (ForgetEnrichment.of (Complex R) X.replacement) Y.source Z.source
  have ht := congrArg (fun k =>
    (𝟙 (homObject R (RightModule R C) X.replacement (M.toFunctor.obj Y.source)) ⊗ₘ
      dgFunctorCommaSourceHomMap R D (RightModule R C) M.toFunctor Y Z) ≫ k) he
  simp only [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp] at ht
  simp only [dgGluingCommaKernelTargetIso_hom]
  exact ht

/-- 第二 primitive の係数合成の可換性は、閉列同型による後合成の自然性。 -/
lemma dgGluingCommaKernelSecondCompositionMap :
    (aXY ⊗ₘ cYZ) ≫
      dgFunctorCommaSecondCompositionMap R (RightModule R D) (RightModule R C)
        F KX KY KZ =
    dgFunctorCommaSecondCompositionMap R D (RightModule R C) M.toFunctor X Y Z ≫ cXZ := by
  simp only [dgFunctorCommaSecondCompositionMap, ← Category.assoc,
    tensorHom_comp_tensorHom, dgGluingCommaKernelHomIso_replacement]
  simp only [dgGluingCommaKernelTargetIso_hom, Category.assoc]
  erw [eComp_eHomWhiskerLeft (Complex R)
    (ForgetEnrichment.of (Complex R) X.replacement)
    (ForgetEnrichment.of (Complex R) Y.replacement)
    (dgGluingKernelColumnIso R C D M (ForgetEnrichment.of (Complex R) Z.source)).inv]
  rw [← Category.assoc]
  erw [tensorHom_comp_whiskerLeft]
  simp only [Category.id_comp]
  rfl

end SerrePositivity.InfinityCategories
