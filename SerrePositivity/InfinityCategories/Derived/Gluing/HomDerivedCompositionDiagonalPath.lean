module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomDerivedCoefficientCompositionLifts
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomDerivedCoefficientDiagonalBoundary
public import SerrePositivity.InfinityCategories.Derived.Gluing.IntervalUncurryHomotopyInverse
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomotopyIntervalPath

/-! 同じ実係数 path を、主比較と同じ二合成対応の対角間の全区間族へ移す。 -/
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

def dgGluingHomDerivedLastCompositionDiagonal (X Y : DGGluingObject R C D M) :=
  dgGluingHomDerivedLastComposition R C D M X Y ≫ compositionCorrespondenceDiagonal
    ((dgGluingUniverseDerivedYoneda.{u, v, w} R C).app (Opposite.op ⦋0⦌)
      (ULift.up (DGNerve.Simplex.vertex X.left))) (dgGluingDerivedAugmentationEdge R C D M Y)

def dgGluingHomDerivedFirstCompositionDiagonal (X Y : DGGluingObject R C D M) :=
  dgGluingHomDerivedFirstComposition R C D M X Y ≫
    dgGluingFirstFixedCompositionDiagonal (dgGluingDerivedAugmentationEdge R C D M X)
      ((dgGluingUniverseDerivedCoefficient R C D M).app (Opposite.op ⦋0⦌)
        (ULift.up (DGNerve.Simplex.vertex Y.right)))

def dgGluingHomDerivedCompositionUncurriedHomotopy (X Y : DGGluingObject R C D M) :
    SSet.Homotopy
      (intervalMappingUncurry (dgGluingHomDerivedLastCompositionDiagonal R C D M X Y))
      (intervalMappingUncurry (dgGluingHomDerivedFirstCompositionDiagonal R C D M X Y)) :=
  stableHomotopyRetarget (dgGluingHomDerivedCoefficientDiagonalHomotopy R C D M X Y)
    (dgGluingHomDerivedLastComposition_diagonal R C D M X Y).symm
    (dgGluingHomDerivedFirstComposition_diagonal R C D M X Y).symm

def dgGluingHomDerivedCompositionDiagonalHomotopy (X Y : DGGluingObject R C D M) :
    SSet.Homotopy (dgGluingHomDerivedLastCompositionDiagonal R C D M X Y)
      (dgGluingHomDerivedFirstCompositionDiagonal R C D M X Y) :=
  dgGluingIntervalUncurryHomotopyInverse
    (dgGluingHomDerivedCompositionUncurriedHomotopy R C D M X Y)
    (dgGluingHomDerivedCoefficientDiagonalHomotopy_source R C D M X Y)
    (dgGluingHomDerivedCoefficientDiagonalHomotopy_target R C D M X Y)

lemma dgGluingHomDerivedCompositionDiagonalHomotopy_evaluate
    (X Y : DGGluingObject R C D M) :
    (α_ (Δ[1] : SSet.{max (u + 1) v w})
        ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
          (complexPinchedSpace.{u, max u v w} (dgGluingHomComplex R C D M X Y)))
        (Δ[1] : SSet.{max (u + 1) v w})).hom ≫
      intervalMappingUncurry (dgGluingHomDerivedCompositionDiagonalHomotopy R C D M X Y).h =
    (dgGluingHomDerivedCoefficientDiagonalHomotopy R C D M X Y).h :=
  dgGluingIntervalUncurryHomotopyInverseMap_evaluate
    (dgGluingHomDerivedCompositionUncurriedHomotopy R C D M X Y)
    (dgGluingHomDerivedCoefficientDiagonalHomotopy_source R C D M X Y)
    (dgGluingHomDerivedCoefficientDiagonalHomotopy_target R C D M X Y)

def dgGluingHomDerivedCompositionDiagonalPath (X Y : DGGluingObject R C D M) :=
  dgGluingHomotopyIntervalPath (dgGluingHomDerivedCompositionDiagonalHomotopy R C D M X Y)

lemma dgGluingHomDerivedCompositionDiagonalPath_start (X Y : DGGluingObject R C D M) :
    dgGluingHomDerivedCompositionDiagonalPath R C D M X Y ≫
        (F2.intervalEndpointNatTrans 0).app _ =
      dgGluingHomDerivedLastCompositionDiagonal R C D M X Y :=
  dgGluingHomotopyIntervalPath_start _

lemma dgGluingHomDerivedCompositionDiagonalPath_end (X Y : DGGluingObject R C D M) :
    dgGluingHomDerivedCompositionDiagonalPath R C D M X Y ≫
        (F2.intervalEndpointNatTrans 1).app _ =
      dgGluingHomDerivedFirstCompositionDiagonal R C D M X Y :=
  dgGluingHomotopyIntervalPath_end _

end SerrePositivity.InfinityCategories
