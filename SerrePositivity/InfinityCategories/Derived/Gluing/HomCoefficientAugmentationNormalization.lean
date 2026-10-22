module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomCoefficientAugmentationCylinder

/-! 元 Hom の負 primitive の明示 augmentation prism と主係数 path を、両端固定で比較する。 -/
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

lemma dgGluingHomCoefficientAugmentationNormalization_exists (X Y : DGGluingObject R C D M) :
    ∃ H : SSet.Homotopy (dgGluingHomCoefficientAugmentationPrism R C D M X Y)
        (uncurry (dgGluingHomCoefficientIntervalPath R C D M X Y)),
      (((SSet.boundary 1).ι ▷
          complexPinchedSpace.{u, max u v w} (dgGluingHomComplex R C D M X Y)) ▷
          (Δ[1] : SSet.{max u v w})) ≫ H.h =
        fst ((SSet.boundary 1 : SSet.{max u v w}) ⊗
            complexPinchedSpace.{u, max u v w} (dgGluingHomComplex R C D M X Y))
          (Δ[1] : SSet.{max u v w}) ≫
          ((SSet.boundary 1).ι ▷
            complexPinchedSpace.{u, max u v w} (dgGluingHomComplex R C D M X Y)) ≫
          uncurry (dgGluingHomCoefficientIntervalPath R C D M X Y) := by
  obtain ⟨H, hH, _⟩ := dgGluingAugmentationCylinderNaturality_exists.{u, max u v w}
    (dgGluingHomTwoEndpointPath R C D M X Y)
  let q := complexPinchedMap.{u, max u v w}
    (dgGluingCoefficientCylinderExtension R C D M X Y)
  let T := functorHomotopyPostcomp H q
  let U := stableHomotopyRetarget T
    (dgGluingHomCoefficientAugmentationCylinder_extension R C D M X Y)
    (dgGluingHomCoefficientIntervalPath_uncurry_cylinder R C D M X Y).symm
  refine ⟨U, ?_⟩
  have hU : U.h = H.h ≫ q := dgGluingHomotopyRetarget_h T _ _
  rw [hU, ← Category.assoc, hH, Category.assoc, Category.assoc]
  exact congrArg (fun z =>
    fst ((SSet.boundary 1 : SSet.{max u v w}) ⊗
        complexPinchedSpace.{u, max u v w} (dgGluingHomComplex R C D M X Y))
      (Δ[1] : SSet.{max u v w}) ≫
      ((SSet.boundary 1).ι ▷
        complexPinchedSpace.{u, max u v w} (dgGluingHomComplex R C D M X Y)) ≫ z)
    (dgGluingHomCoefficientIntervalPath_uncurry_cylinder R C D M X Y).symm

end SerrePositivity.InfinityCategories
