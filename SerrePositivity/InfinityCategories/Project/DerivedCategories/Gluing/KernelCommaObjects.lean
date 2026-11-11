module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.KernelHomAction
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ConeObjectTransport

/-! 同じ通常 kernel の加群 comma 内で、元の gluing 対象と標準円錐を表示する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)

/-- 元の gluing 対象を、両側の代表加群と同じ augmentation の kernel 持ち上げで表示。 -/
def dgGluingKernelObject (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R (RightModule R D) (RightModule R C) (Morita.kernelTensor R D C M) where
  source := representable R X.right
  replacement := representable R X.left
  augmentation := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelLift R C D M X

variable (Y Z : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
  (f : ForgetEnrichment.of (Complex R) Y ⟶ ForgetEnrichment.of (Complex R) Z)

/-- 元の実 cone 比較射を、同じ右 Yoneda 円錐の通常 tensor 像へ送る実加群射。 -/
def dgGluingConeKernelMorphism :
    moduleCone R C (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeLeftArrow R C D M Y Z f) ⟶
    (Morita.kernelTensor R D C M).onClosed.obj (moduleCone R D
      ((dgYoneda R D).onClosed.map ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight R C D M).onClosed.map f))) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeMorphism R C D M Y Z f ≫
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaKernelConeIso R C D M
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M Y) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M Z)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToComma R C D M).onClosed.map f)).hom

/-- 加群 comma 内の、元の両成分の標準円錐と同じ実比較射を持つ対象。 -/
def dgGluingKernelConeObject :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R (RightModule R D) (RightModule R C) (Morita.kernelTensor R D C M) where
  source := ForgetEnrichment.to (Complex R) (moduleCone R D
    ((dgYoneda R D).onClosed.map ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight R C D M).onClosed.map f)))
  replacement := ForgetEnrichment.to (Complex R)
    (moduleCone R C (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeLeftArrow R C D M Y Z f))
  augmentation := dgGluingConeKernelMorphism R C D M Y Z f

variable (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)

/-- 標準円錐への加群 comma の右作用は、構成済みの同じ kernel 全 Hom 作用。 -/
lemma dgGluingKernelConeDifference_inl :
    biprod.inl ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaDifference R (RightModule R D) (RightModule R C)
      (Morita.kernelTensor R D C M) (dgGluingKernelObject R C D M X)
      (dgGluingKernelConeObject R C D M Y Z f) =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelHomAction R C D M X
      (dgGluingKernelConeObject R C D M Y Z f).source := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaDifference, Preadditive.comp_sub]
  erw [biprod.inl_fst_assoc, biprod.inl_snd_assoc]
  simp only [zero_comp, sub_zero]
  rfl

/-- 左作用は、同じ実 cone 比較射と tensor 比較の合成の後合成の負。 -/
lemma dgGluingKernelConeDifference_inr :
    biprod.inr ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaDifference R (RightModule R D) (RightModule R C)
      (Morita.kernelTensor R D C M) (dgGluingKernelObject R C D M X)
      (dgGluingKernelConeObject R C D M Y Z f) =
    -eHomWhiskerLeft (Complex R)
      (ForgetEnrichment.of (Complex R) (representable R X.left))
      (dgGluingConeKernelMorphism R C D M Y Z f) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaDifference, Preadditive.comp_sub]
  erw [biprod.inr_fst_assoc, biprod.inr_snd_assoc]
  simp only [zero_comp, zero_sub]
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
