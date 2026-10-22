module
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativeCoefficientActions
public import SerrePositivity.InfinityCategories.Derived.Gluing.ClosedPrecompositionAW
public import SerrePositivity.InfinityCategories.Derived.DGPinchedFamilyComposition

/-! 元の augmentation と二入力の実 AW 合成族は、元の二作用そのものである。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

lemma dgGluingNativeLeftCoefficientComposition (X Y : DGGluingObject R C D M) :
    pinchedHomCompositionFamily (dgGluingNativeLeftCoefficientInput R C D M X Y)
        (SSet.const (pinchedClosedVertex R (RightModule R C)
          (dgGluingAugmentation R C D M Y))) =
      complexPinchedMap.{u, max (u + 1) v} (dgGluingLeftAction R C D M X Y) ≫
        (dgGluingCoefficientYonedaSpaceIso R C X.left (M.rightAt Y.right)).hom := by
  rw [pinchedHomCompositionFamily_closed_post]
  exact (dgGluingNativeLeftCoefficientAction R C D M X Y).symm

lemma dgGluingNativeRightCoefficientComposition (X Y : DGGluingObject R C D M) :
    pinchedHomCompositionFamily
        (SSet.const (pinchedClosedVertex R (RightModule R C)
          (dgGluingAugmentation R C D M X)))
        (dgGluingNativeRightCoefficientInput R C D M X Y) =
      complexPinchedMap.{u, max (u + 1) v} (dgGluingRightAction R C D M X Y) ≫
        (dgGluingCoefficientYonedaSpaceIso R C X.left (M.rightAt Y.right)).hom := by
  rw [dgGluingPinchedCompositionFamily_closed_pre]
  exact (dgGluingNativeRightCoefficientAction R C D M X Y).symm

lemma dgGluingNativeLeftCoefficientFamily_comp (X Y : DGGluingObject R C D M) :
    dgPinchedFamilyHom R (RightModule R C) (dgGluingNativeLeftCoefficientInput R C D M X Y) ≫
        dgPinchedFamilyHom R (RightModule R C)
          (SSet.const (pinchedClosedVertex R (RightModule R C)
            (dgGluingAugmentation R C D M Y))) =
      dgPinchedFamilyHom R (RightModule R C)
        (complexPinchedMap.{u, max (u + 1) v} (dgGluingLeftAction R C D M X Y) ≫
          (dgGluingCoefficientYonedaSpaceIso R C X.left (M.rightAt Y.right)).hom) := by
  rw [dgPinchedFamilyHom_comp, dgGluingNativeLeftCoefficientComposition R C D M X Y]

lemma dgGluingNativeRightCoefficientFamily_comp (X Y : DGGluingObject R C D M) :
    dgPinchedFamilyHom R (RightModule R C)
        (SSet.const (pinchedClosedVertex R (RightModule R C)
          (dgGluingAugmentation R C D M X))) ≫
        dgPinchedFamilyHom R (RightModule R C)
          (dgGluingNativeRightCoefficientInput R C D M X Y) =
      dgPinchedFamilyHom R (RightModule R C)
        (complexPinchedMap.{u, max (u + 1) v} (dgGluingRightAction R C D M X Y) ≫
          (dgGluingCoefficientYonedaSpaceIso R C X.left (M.rightAt Y.right)).hom) := by
  rw [dgPinchedFamilyHom_comp, dgGluingNativeRightCoefficientComposition R C D M X Y]

end SerrePositivity.InfinityCategories
