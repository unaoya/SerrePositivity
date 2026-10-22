module
public import SerrePositivity.InfinityCategories.Derived.Gluing.ComplexCochainAugmentationHomotopy
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomCoefficientDirectCylinder

/-! 元 Hom の二作用と負 primitive を、元 augmentation 構成に基づく全実区間族へ移す。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded MonoidalCategory
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

def dgGluingHomCoefficientAugmentationPrism (X Y : DGGluingObject R C D M) :=
  dgGluingComplexCochainAugmentationPrism.{u, max u v w}
    (dgGluingLeftHomMap R C D M X Y ≫ dgGluingLeftAction R C D M X Y)
    (dgGluingRightHomMap R C D M X Y ≫ dgGluingRightAction R C D M X Y)
    (-dgGluingHomPrimitive R C D M X Y) (dgGluingHomNegativePrimitive_boundary R C D M X Y)

lemma dgGluingHomCoefficientAugmentationPrism_zero (X Y : DGGluingObject R C D M) :
    prismEndpoint 0 _ ≫ dgGluingHomCoefficientAugmentationPrism R C D M X Y =
      complexPinchedMap.{u, max u v w}
        (dgGluingLeftHomMap R C D M X Y ≫ dgGluingLeftAction R C D M X Y) :=
  dgGluingComplexCochainAugmentationPrism_zero _ _ _ _

lemma dgGluingHomCoefficientAugmentationPrism_one (X Y : DGGluingObject R C D M) :
    prismEndpoint 1 _ ≫ dgGluingHomCoefficientAugmentationPrism R C D M X Y =
      complexPinchedMap.{u, max u v w}
        (dgGluingRightHomMap R C D M X Y ≫ dgGluingRightAction R C D M X Y) :=
  dgGluingComplexCochainAugmentationPrism_one _ _ _ _

def dgGluingHomCoefficientAugmentationHomotopy (X Y : DGGluingObject R C D M) :=
  dgGluingHomotopyOfPrism (dgGluingHomCoefficientAugmentationPrism R C D M X Y)
    (dgGluingHomCoefficientAugmentationPrism_zero R C D M X Y)
    (dgGluingHomCoefficientAugmentationPrism_one R C D M X Y)

lemma dgGluingHomCoefficientAugmentationHomotopy_h (X Y : DGGluingObject R C D M) :
    (dgGluingHomCoefficientAugmentationHomotopy R C D M X Y).h =
      (β_ (complexPinchedSpace.{u, max u v w} (dgGluingHomComplex R C D M X Y))
        (Δ[1] : SSet.{max u v w})).hom ≫
        dgGluingHomCoefficientAugmentationPrism R C D M X Y := rfl

end SerrePositivity.InfinityCategories
