module
public import SerrePositivity.InfinityCategories.Derived.Gluing.PinchedEndpointUncurry
public import SerrePositivity.InfinityCategories.Derived.Gluing.LaxHomArrowTriangleEvaluations

/-! 元の lax Hom の可変二辺は、元の全 pinched 族と augmentation 全矢印族の成分評価。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory MonoidalClosed DifferentialGraded DGNerve SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

lemma dgGluingLaxHomArrowComponent_uncurry (X Y : DGGluingObject R C D M) (i : Fin 2) :
    intervalMappingUncurry (dgGluingLaxHomArrowComponent R C D M X Y i) =
      rightMappingSpacePrism
          ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
            (complexPinchedSpace.{u, max u v w} (dgGluingHomComplex R C D M X Y))) ≫
        pinchedHomUncurry (dgGluingUniverseHomMappingIso R C D M X Y).inv ≫
          dgGluingUniverseDerivedAugmentationArrowFamily R C D M ≫
            evaluateFunctorAt (stdSimplex.obj₀Equiv.symm i) := by
  rw [dgGluingLaxHomArrowComponent, intervalMappingPostOfEq_uncurry,
    dgGluingLaxHomArrowIntervalComparison_action R C D M X Y]
  have hu := dgGluingPinchedEndpointIso_interval_uncurry
    (dgGluingDerivedAugmentationArrowDiagram_vertex R C D M X)
    (dgGluingDerivedAugmentationArrowDiagram_vertex R C D M Y)
    ((dgGluingUniverseHomMappingIso R C D M X Y).inv ≫
      pinchedHomMap (dgGluingUniverseDerivedAugmentationArrowFamily R C D M)
        (ULift.up (Simplex.vertex X)) (ULift.up (Simplex.vertex Y)))
  simp only [Category.assoc] at hu
  rw [hu, pinchedHomUncurry_postcomp]
  simp only [Category.assoc]

lemma dgGluingLaxHomArrowComponent_source (X Y : DGGluingObject R C D M) :
    intervalMappingUncurry (dgGluingLaxHomArrowComponent R C D M X Y 0) =
      rightMappingSpacePrism
          ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
            (complexPinchedSpace.{u, max u v w} (dgGluingHomComplex R C D M X Y))) ≫
        pinchedHomUncurry (dgGluingUniverseHomMappingIso R C D M X Y).inv ≫
          dgGluingUniverseLeftNerve R C D M ≫ dgGluingUniverseDerivedYoneda.{u, v, w} R C := by
  rw [dgGluingLaxHomArrowComponent_uncurry R C D M X Y 0,
    dgGluingUniverseDerivedAugmentationArrowFamily_source R C D M]

lemma dgGluingLaxHomArrowComponent_target (X Y : DGGluingObject R C D M) :
    intervalMappingUncurry (dgGluingLaxHomArrowComponent R C D M X Y 1) =
      rightMappingSpacePrism
          ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
            (complexPinchedSpace.{u, max u v w} (dgGluingHomComplex R C D M X Y))) ≫
        pinchedHomUncurry (dgGluingUniverseHomMappingIso R C D M X Y).inv ≫
          dgGluingUniverseRightNerve R C D M ≫ dgGluingUniverseDerivedCoefficient R C D M := by
  rw [dgGluingLaxHomArrowComponent_uncurry R C D M X Y 1,
    dgGluingUniverseDerivedAugmentationArrowFamily_target R C D M]

end SerrePositivity.InfinityCategories
