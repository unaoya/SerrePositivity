module
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativeCoefficientComposition
public import SerrePositivity.InfinityCategories.Derived.DGPinchedCompositionFamilyPrism

/-! 二作用を表す元の augmentation の実合成 prism と、その両端・全射影。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

def dgGluingNativeLeftCoefficientCompositionPrism (X Y : DGGluingObject R C D M) :=
  dgPinchedCompositionFamilyPrism R (RightModule R C)
    (dgGluingNativeLeftCoefficientInput R C D M X Y)
    (SSet.const (pinchedClosedVertex R (RightModule R C) (dgGluingAugmentation R C D M Y)))

def dgGluingNativeRightCoefficientCompositionPrism (X Y : DGGluingObject R C D M) :=
  dgPinchedCompositionFamilyPrism R (RightModule R C)
    (SSet.const (pinchedClosedVertex R (RightModule R C) (dgGluingAugmentation R C D M X)))
    (dgGluingNativeRightCoefficientInput R C D M X Y)

lemma dgGluingNativeLeftCoefficientCompositionPrism_zero (X Y : DGGluingObject R C D M) :
    prismEndpoint 0 _ ≫ dgGluingNativeLeftCoefficientCompositionPrism R C D M X Y =
      (complexPinchedMap.{u, max (u + 1) v} (dgGluingLeftAction R C D M X Y) ≫
        (dgGluingCoefficientYonedaSpaceIso R C X.left (M.rightAt Y.right)).hom) ≫
          dgPinchedHomSlice R (RightModule R C) (representable R X.left) (M.rightAt Y.right) := by
  have h := dgPinchedCompositionFamilyPrism_zero R (RightModule R C)
    (dgGluingNativeLeftCoefficientInput R C D M X Y)
    (SSet.const (pinchedClosedVertex R (RightModule R C) (dgGluingAugmentation R C D M Y)))
  rw [dgGluingNativeLeftCoefficientComposition R C D M X Y] at h
  exact h

lemma dgGluingNativeRightCoefficientCompositionPrism_zero (X Y : DGGluingObject R C D M) :
    prismEndpoint 0 _ ≫ dgGluingNativeRightCoefficientCompositionPrism R C D M X Y =
      (complexPinchedMap.{u, max (u + 1) v} (dgGluingRightAction R C D M X Y) ≫
        (dgGluingCoefficientYonedaSpaceIso R C X.left (M.rightAt Y.right)).hom) ≫
          dgPinchedHomSlice R (RightModule R C) (representable R X.left) (M.rightAt Y.right) := by
  have h := dgPinchedCompositionFamilyPrism_zero R (RightModule R C)
    (SSet.const (pinchedClosedVertex R (RightModule R C) (dgGluingAugmentation R C D M X)))
    (dgGluingNativeRightCoefficientInput R C D M X Y)
  rw [dgGluingNativeRightCoefficientComposition R C D M X Y] at h
  exact h

lemma dgGluingNativeLeftCoefficientCompositionPrism_one (X Y : DGGluingObject R C D M) :
    prismEndpoint 1 _ ≫ dgGluingNativeLeftCoefficientCompositionPrism R C D M X Y =
      SSet.const (pinchedClosedVertex R (RightModule R C) (dgGluingAugmentation R C D M Y)) ≫
        dgPinchedHomSlice R (RightModule R C) (representable R Y.left) (M.rightAt Y.right) :=
  dgPinchedCompositionFamilyPrism_one R (RightModule R C) _ _

lemma dgGluingNativeRightCoefficientCompositionPrism_one (X Y : DGGluingObject R C D M) :
    prismEndpoint 1 _ ≫ dgGluingNativeRightCoefficientCompositionPrism R C D M X Y =
      dgGluingNativeRightCoefficientInput R C D M X Y ≫
        dgPinchedHomSlice R (RightModule R C) (M.rightAt X.right) (M.rightAt Y.right) :=
  dgPinchedCompositionFamilyPrism_one R (RightModule R C) _ _

lemma dgGluingNativeLeftCoefficientCompositionPrism_projection (X Y : DGGluingObject R C D M) :
    dgGluingNativeLeftCoefficientCompositionPrism R C D M X Y ≫ sliceOverProjection _ =
      intervalMappingUncurry (dgGluingNativeLeftCoefficientInput R C D M X Y ≫
        pinchedHomToIntervalMappingSpace
          (X := dgNerve R (RightModule R C))
          (DGNerve.Simplex.vertex (representable R X.left))
          (DGNerve.Simplex.vertex (representable R Y.left))) :=
  dgPinchedCompositionFamilyPrism_projection R (RightModule R C) _ _

lemma dgGluingNativeRightCoefficientCompositionPrism_projection (X Y : DGGluingObject R C D M) :
    dgGluingNativeRightCoefficientCompositionPrism R C D M X Y ≫ sliceOverProjection _ =
      intervalMappingUncurry
        (SSet.const (pinchedClosedVertex R (RightModule R C) (dgGluingAugmentation R C D M X)) ≫
          pinchedHomToIntervalMappingSpace
            (X := dgNerve R (RightModule R C))
            (DGNerve.Simplex.vertex (representable R X.left))
            (DGNerve.Simplex.vertex (M.rightAt X.right))) :=
  dgPinchedCompositionFamilyPrism_projection R (RightModule R C) _ _

end SerrePositivity.InfinityCategories
