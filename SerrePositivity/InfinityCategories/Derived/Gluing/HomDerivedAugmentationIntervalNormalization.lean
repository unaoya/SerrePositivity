module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomDerivedAugmentationNormalization
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomDerivedCoefficientIntervalPrism

/-! 明示 augmentation を主比較の区間 Hom へ移し、同じ係数対角の全区間族と両端固定で比較。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory DifferentialGraded
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

def dgGluingHomDerivedAugmentationIntervalPrism (X Y : DGGluingObject R C D M) :=
  dgGluingHomDerivedAugmentationPrism R C D M X Y ≫
    (dgGluingDerivedCoefficientEndpointIso R C D M X.left Y.right).inv ≫
      pinchedHomToIntervalMappingSpace _ _

lemma dgGluingHomDerivedAugmentationIntervalNormalization_exists
    (X Y : DGGluingObject R C D M) :
    ∃ H : SSet.Homotopy (dgGluingHomDerivedAugmentationIntervalPrism R C D M X Y)
        (dgGluingHomDerivedCoefficientIntervalPrism R C D M X Y),
      (((SSet.boundary 1).ι ▷ (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
          (complexPinchedSpace.{u, max u v w} (dgGluingHomComplex R C D M X Y))) ▷
          (Δ[1] : SSet.{max (u + 1) v w})) ≫ H.h =
        fst ((SSet.boundary 1 : SSet.{max (u + 1) v w}) ⊗
            (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
              (complexPinchedSpace.{u, max u v w} (dgGluingHomComplex R C D M X Y))) Δ[1] ≫
          ((SSet.boundary 1).ι ▷ (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
            (complexPinchedSpace.{u, max u v w} (dgGluingHomComplex R C D M X Y))) ≫
              dgGluingHomDerivedCoefficientIntervalPrism R C D M X Y := by
  obtain ⟨H, hH⟩ := dgGluingHomDerivedAugmentationNormalization_exists R C D M X Y
  let q := (dgGluingDerivedCoefficientEndpointIso R C D M X.left Y.right).inv ≫
    pinchedHomToIntervalMappingSpace _ _
  have he : uncurry (dgGluingDerivedHomCoefficientIntervalPath R C D M X Y) ≫ q =
      dgGluingHomDerivedCoefficientIntervalPrism R C D M X Y :=
    (dgGluingHomDerivedCoefficientIntervalPrism_eq R C D M X Y).symm
  let T := functorHomotopyPostcomp H q
  let U := stableHomotopyRetarget T rfl he
  refine ⟨U, ?_⟩
  have hU : U.h = H.h ≫ q := dgGluingHomotopyRetarget_h T _ _
  rw [hU, ← Category.assoc, hH, Category.assoc, Category.assoc, he]

end SerrePositivity.InfinityCategories
