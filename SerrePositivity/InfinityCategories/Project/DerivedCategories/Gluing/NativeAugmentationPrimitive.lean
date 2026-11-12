module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.PrimitiveComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomCoefficientCylinderCoefficients
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGCommaAugHomotopyData

/-! 元の実 augmentation の比較成分は Yoneda 像の元 Hom primitive であり、主円柱はその負号。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory CochainComplex HomComplex DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

lemma dgGluingNativeAugmentationHomotopyComponent (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
    (p : ℤ) (z : GradedHom R X Y p) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationHomotopyComponent R D (RightModule R C) M.toFunctor
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M X) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M Y) p
        (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToComma R C D M).map X Y).f p z) =
      (dgYonedaIso R X.left (M.rightAt Y.right)).inv.f (p - 1)
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomPrimitive R C D M X Y).v p (p - 1) (by omega) z) := by
  exact ConcreteCategory.congr_hom
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomRepresentableIso_primitive_v R C D M X Y p (p - 1) (by omega)) z

lemma dgGluingNativeAugmentationCylinderPrimitive (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
    (p : ℤ) (z : GradedHom R X Y p) :
    (dgYonedaIso R X.left (M.rightAt Y.right)).inv.f (p - 1)
        (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainCylinderPrimitive (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComplex R C D M X Y)).comp
          (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomCoefficientCylinderExtension R C D M X Y))
          (add_zero (-1))).v p (p - 1) (by omega) z) =
      -_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationHomotopyComponent R D (RightModule R C) M.toFunctor
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M X) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M Y) p
        (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToComma R C D M).map X Y).f p z) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomCoefficientCylinderExtension_primitive, Cochain.neg_v]
  simp only [ModuleCat.hom_neg, LinearMap.neg_apply, map_neg]
  exact congrArg Neg.neg (dgGluingNativeAugmentationHomotopyComponent R C D M X Y p z).symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
