module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomConeRightKernelComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ConeObjectTransport

/-! 左右 Hom 円錐の係数で使用した標的同型を揃える。 -/
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
local notation "B" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M Y
local notation "C'" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M Z
local notation "cf" => CategoryTheory.Functor.map
  (SerrePositivity.DifferentialGraded.DGFunctor.onClosed (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToComma R C D M)) f
local notation "k" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaKernelConeIso R C D M B C' cf
local notation "T" => ForgetEnrichment.of (Complex R) (representable R X.left)

/-- 左係数の標的に同じ tensor 比較を続けると、右係数の標的同型と厳密に一致する。 -/
lemma dgGluingHomConeTarget_comparison :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeRightTensorTargetIso R C D M X Y Z f).hom =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeImageModuleIso R C D M X Y Z f).hom ≫
      eHomWhiskerLeft (Complex R) T (k).hom := by
  have hn := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingYoneda_postcompose_inv R C X.left (k).hom
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeRightTensorTargetIso, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeImageModuleIso,
    Iso.trans_hom, Iso.symm_hom, CategoryTheory.Functor.mapIso_hom]
  erw [Category.assoc, ← hn]
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaKernelConeIso, Iso.trans_hom, eqToIso.hom,
    eqToHom_refl, Category.id_comp]
  rfl

/-- 左係数も同じ tensor 標的に移すと、元の cone 比較と tensor 比較の合成の後合成になる。 -/
lemma dgGluingHomConeLeftCoefficient_kernel_module :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeLeftCoefficient R C D M X Y Z f ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeRightTensorTargetIso R C D M X Y Z f).hom =
    -((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeLeftModuleIso R C D M X Y Z f).hom ≫
      eHomWhiskerLeft (Complex R) T (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeMorphism R C D M Y Z f ≫ (k).hom)) := by
  rw [dgGluingHomConeTarget_comparison, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeLeftCoefficient_module, Preadditive.neg_comp, Category.assoc]
  erw [← eHomWhiskerLeft_comp (Complex R) T (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeMorphism R C D M Y Z f) (k).hom]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
