module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.CommaKernelProjections
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.TensorPrimitiveTransport

/-! kernel comma 比較は、全 Hom tensor 上の二つの primitive の係数合成を保つ。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits DifferentialGraded MonoidalCategory CochainComplex HomComplex
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (X Y Z : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R D (RightModule R C) M.toFunctor)
local notation "F" => Morita.kernelTensor R D C M
local notation "KX" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaKernelObject R C D M X
local notation "KY" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaKernelObject R C D M Y
local notation "KZ" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaKernelObject R C D M Z
local notation "aXY" => Iso.hom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaKernelHomIso R C D M X Y)
local notation "aYZ" => Iso.hom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaKernelHomIso R C D M Y Z)
local notation "aXZ" => Iso.hom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaKernelHomIso R C D M X Z)
local notation "cXY" => Iso.hom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaKernelTargetIso R C D M X Y)
local notation "cYZ" => Iso.hom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaKernelTargetIso R C D M Y Z)
local notation "cXZ" => Iso.hom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaKernelTargetIso R C D M X Z)

/-- 第一 primitive の係数合成の可換性は、列比較の全 Hom 自然性による。 -/
lemma dgGluingCommaKernelFirstCompositionMap :
    (cXY ⊗ₘ aYZ) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaFirstCompositionMap R (RightModule R D) (RightModule R C)
        F KX KY KZ =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaFirstCompositionMap R D (RightModule R C) M.toFunctor X Y Z ≫ cXZ := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaFirstCompositionMap, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaImageHomMap,
    ← Category.assoc, tensorHom_comp_tensorHom]
  simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaKernelHomIso_source]
  have he := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelColumnIso_inv_composition R C D M
    (ForgetEnrichment.of (Complex R) X.replacement) Y.source Z.source
  have ht := congrArg (fun k =>
    (𝟙 (homObject R (RightModule R C) X.replacement (M.toFunctor.obj Y.source)) ⊗ₘ
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSourceHomMap R D (RightModule R C) M.toFunctor Y Z) ≫ k) he
  simp only [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp] at ht
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaKernelTargetIso_hom]
  exact ht

/-- 第二 primitive の係数合成の可換性は、閉列同型による後合成の自然性。 -/
lemma dgGluingCommaKernelSecondCompositionMap :
    (aXY ⊗ₘ cYZ) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSecondCompositionMap R (RightModule R D) (RightModule R C)
        F KX KY KZ =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSecondCompositionMap R D (RightModule R C) M.toFunctor X Y Z ≫ cXZ := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSecondCompositionMap, ← Category.assoc,
    tensorHom_comp_tensorHom, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaKernelHomIso_replacement]
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaKernelTargetIso_hom, Category.assoc]
  erw [eComp_eHomWhiskerLeft (Complex R)
    (ForgetEnrichment.of (Complex R) X.replacement)
    (ForgetEnrichment.of (Complex R) Y.replacement)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelColumnIso R C D M (ForgetEnrichment.of (Complex R) Z.source)).inv]
  rw [← Category.assoc]
  erw [tensorHom_comp_whiskerLeft]
  simp only [Category.id_comp]
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
