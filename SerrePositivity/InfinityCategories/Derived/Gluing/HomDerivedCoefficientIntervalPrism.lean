module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomDerivedCoefficientDiagonalHomotopy
public import SerrePositivity.InfinityCategories.Derived.Gluing.IntervalPathHomotopyPrism

/-! 主係数対角の実ホモトピーを、区間第一因子の同じ全 prism として保持する。 -/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory MonoidalClosed DifferentialGraded
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

def dgGluingHomDerivedCoefficientIntervalPrism (X Y : DGGluingObject R C D M) :=
  (β_ (Δ[1] : SSet.{max (u + 1) v w})
    ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
      (complexPinchedSpace.{u, max u v w} (dgGluingHomComplex R C D M X Y)))).hom ≫
    (dgGluingHomDerivedCoefficientIntervalHomotopy R C D M X Y).h

lemma dgGluingHomDerivedCoefficientIntervalPrism_eq (X Y : DGGluingObject R C D M) :
    dgGluingHomDerivedCoefficientIntervalPrism R C D M X Y =
      uncurry (dgGluingDerivedHomCoefficientIntervalPath R C D M X Y) ≫
        (dgGluingDerivedCoefficientEndpointIso R C D M X.left Y.right).inv ≫
          pinchedHomToIntervalMappingSpace _ _ :=
  dgGluingIntervalPathHomotopy_post_prism
    (dgGluingDerivedHomCoefficientIntervalPath R C D M X Y) _

end SerrePositivity.InfinityCategories
