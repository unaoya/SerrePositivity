module
public import SerrePositivity.InfinityCategories.Derived.Gluing.PrimitiveComparison
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomCoefficientCylinderCoefficients
public import SerrePositivity.InfinityCategories.Derived.DGCommaAugHomotopyData

/-! 元の実 augmentation の比較成分は Yoneda 像の元 Hom primitive であり、主円柱はその負号。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory CochainComplex HomComplex DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

lemma dgGluingNativeAugmentationHomotopyComponent (X Y : DGGluingObject R C D M)
    (p : ℤ) (z : GradedHom R X Y p) :
    dgCommaAugmentationHomotopyComponent R D (RightModule R C) M.toFunctor
        (dgGluingCommaObject R C D M X) (dgGluingCommaObject R C D M Y) p
        (((dgGluingToComma R C D M).map X Y).f p z) =
      (dgYonedaIso R X.left (M.rightAt Y.right)).inv.f (p - 1)
        ((dgGluingHomPrimitive R C D M X Y).v p (p - 1) (by omega) z) := by
  exact ConcreteCategory.congr_hom
    (dgGluingHomRepresentableIso_primitive_v R C D M X Y p (p - 1) (by omega)) z

lemma dgGluingNativeAugmentationCylinderPrimitive (X Y : DGGluingObject R C D M)
    (p : ℤ) (z : GradedHom R X Y p) :
    (dgYonedaIso R X.left (M.rightAt Y.right)).inv.f (p - 1)
        (((dgGluingCochainCylinderPrimitive (dgGluingHomComplex R C D M X Y)).comp
          (Cochain.ofHom (dgGluingHomCoefficientCylinderExtension R C D M X Y))
          (add_zero (-1))).v p (p - 1) (by omega) z) =
      -dgCommaAugmentationHomotopyComponent R D (RightModule R C) M.toFunctor
        (dgGluingCommaObject R C D M X) (dgGluingCommaObject R C D M Y) p
        (((dgGluingToComma R C D M).map X Y).f p z) := by
  rw [dgGluingHomCoefficientCylinderExtension_primitive, Cochain.neg_v]
  simp only [ModuleCat.hom_neg, LinearMap.neg_apply, map_neg]
  exact congrArg Neg.neg (dgGluingNativeAugmentationHomotopyComponent R C D M X Y p z).symm

end SerrePositivity.InfinityCategories
