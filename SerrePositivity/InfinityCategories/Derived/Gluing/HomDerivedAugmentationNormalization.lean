module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomCoefficientAugmentationNormalization
public import SerrePositivity.InfinityCategories.Derived.Gluing.UliftPrismHomotopyBoundary
public import SerrePositivity.InfinityCategories.Derived.Gluing.UliftPrismUncurry
public import SerrePositivity.InfinityCategories.Derived.Gluing.DerivedHomCoefficientPathLegs

/-! 元 Hom の明示 augmentation prism と canonical 導来係数 path を、全パラメーター・両端固定で比較。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory DifferentialGraded
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

def dgGluingHomDerivedAugmentationPrism (X Y : DGGluingObject R C D M) :=
  dgGluingUliftSimplexFamily.{max u v w, max (u + 1) v w} 1
      (dgGluingHomCoefficientAugmentationPrism R C D M X Y) ≫
    dgGluingCanonicalCoefficientMappingComparison R C D M X.left Y.right

lemma dgGluingHomDerivedAugmentationNormalization_exists (X Y : DGGluingObject R C D M) :
    ∃ H : SSet.Homotopy (dgGluingHomDerivedAugmentationPrism R C D M X Y)
        (uncurry (dgGluingDerivedHomCoefficientIntervalPath R C D M X Y)),
      (((SSet.boundary 1).ι ▷ (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
          (complexPinchedSpace.{u, max u v w} (dgGluingHomComplex R C D M X Y))) ▷
          (Δ[1] : SSet.{max (u + 1) v w})) ≫ H.h =
        fst ((SSet.boundary 1 : SSet.{max (u + 1) v w}) ⊗
            (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
              (complexPinchedSpace.{u, max u v w} (dgGluingHomComplex R C D M X Y))) Δ[1] ≫
          ((SSet.boundary 1).ι ▷ (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
            (complexPinchedSpace.{u, max u v w} (dgGluingHomComplex R C D M X Y))) ≫
              uncurry (dgGluingDerivedHomCoefficientIntervalPath R C D M X Y) := by
  obtain ⟨H, hH⟩ := dgGluingHomCoefficientAugmentationNormalization_exists R C D M X Y
  have he : dgGluingUliftSimplexFamily.{max u v w, max (u + 1) v w} 1
        (uncurry (dgGluingHomCoefficientIntervalPath R C D M X Y)) ≫
      dgGluingCanonicalCoefficientMappingComparison R C D M X.left Y.right =
        uncurry (dgGluingDerivedHomCoefficientIntervalPath R C D M X Y) := by
    rw [dgGluingUliftPrism_uncurry]
    exact (dgGluingDerivedHomCoefficientIntervalPath_uncurry R C D M X Y).symm
  let T := functorHomotopyPostcomp
    (dgGluingUliftPrismHomotopy.{max u v w, max (u + 1) v w} H)
    (dgGluingCanonicalCoefficientMappingComparison R C D M X.left Y.right)
  let U := stableHomotopyRetarget T rfl he
  refine ⟨U, ?_⟩
  have hU : U.h = (dgGluingUliftPrismHomotopy.{max u v w, max (u + 1) v w} H).h ≫
      dgGluingCanonicalCoefficientMappingComparison R C D M X.left Y.right :=
    dgGluingHomotopyRetarget_h T _ _
  rw [hU, ← Category.assoc, dgGluingUliftPrismHomotopy_boundary H hH,
    Category.assoc, Category.assoc, he]

end SerrePositivity.InfinityCategories
