module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomDerivedCoefficientCompositionLifts
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomDerivedCoefficientDiagonalBoundary
public import SerrePositivity.InfinityCategories.Derived.Gluing.IntervalUncurryHomotopyInverse
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomotopyIntervalPath
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomotopyRetargetValue

/-! 同じ実係数 path を、主比較と同じ二合成対応の対角間の全区間族へ移す。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded
open scoped _root_.Simplicial
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

lemma dgGluingHomDerivedCompositionUncurriedHomotopy_h (X Y : DGGluingObject R C D M) :
    (dgGluingHomDerivedCompositionUncurriedHomotopy R C D M X Y).h =
      (dgGluingHomDerivedCoefficientDiagonalHomotopy R C D M X Y).h := by
  exact dgGluingHomotopyRetarget_h
    (dgGluingHomDerivedCoefficientDiagonalHomotopy R C D M X Y)
    (dgGluingHomDerivedLastComposition_diagonal R C D M X Y).symm
    (dgGluingHomDerivedFirstComposition_diagonal R C D M X Y).symm

lemma dgGluingHomDerivedCompositionUncurriedHomotopy_source (X Y : DGGluingObject R C D M) :
    (prismEndpoint 0 _ ▷ (Δ[1] : SSet.{max (u + 1) v w})) ≫
        (dgGluingHomDerivedCompositionUncurriedHomotopy R C D M X Y).h =
      SSet.const ((dgGluingUniverseDerivedYoneda.{u, v, w} R C).app (Opposite.op ⦋0⦌)
        (ULift.up (DGNerve.Simplex.vertex X.left))) := by
  rw [dgGluingHomDerivedCompositionUncurriedHomotopy_h R C D M X Y]
  exact dgGluingHomDerivedCoefficientDiagonalHomotopy_source R C D M X Y

lemma dgGluingHomDerivedCompositionUncurriedHomotopy_target (X Y : DGGluingObject R C D M) :
    (prismEndpoint 1 _ ▷ (Δ[1] : SSet.{max (u + 1) v w})) ≫
        (dgGluingHomDerivedCompositionUncurriedHomotopy R C D M X Y).h =
      SSet.const ((dgGluingUniverseDerivedCoefficient R C D M).app (Opposite.op ⦋0⦌)
        (ULift.up (DGNerve.Simplex.vertex Y.right))) := by
  rw [dgGluingHomDerivedCompositionUncurriedHomotopy_h R C D M X Y]
  exact dgGluingHomDerivedCoefficientDiagonalHomotopy_target R C D M X Y

def dgGluingHomDerivedCompositionDiagonalHomotopy (X Y : DGGluingObject R C D M) :
    SSet.Homotopy (dgGluingHomDerivedLastCompositionDiagonal R C D M X Y)
      (dgGluingHomDerivedFirstCompositionDiagonal R C D M X Y) :=
  dgGluingIntervalUncurryHomotopyInverse
    (dgGluingHomDerivedCompositionUncurriedHomotopy R C D M X Y)
    (dgGluingHomDerivedCompositionUncurriedHomotopy_source R C D M X Y)
    (dgGluingHomDerivedCompositionUncurriedHomotopy_target R C D M X Y)

lemma dgGluingHomDerivedCompositionDiagonalHomotopy_evaluate
    (X Y : DGGluingObject R C D M) :
    (α_ (Δ[1] : SSet.{max (u + 1) v w})
        ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
          (complexPinchedSpace.{u, max u v w} (dgGluingHomComplex R C D M X Y)))
        (Δ[1] : SSet.{max (u + 1) v w})).hom ≫
      intervalMappingUncurry (dgGluingHomDerivedCompositionDiagonalHomotopy R C D M X Y).h =
    (dgGluingHomDerivedCoefficientDiagonalHomotopy R C D M X Y).h :=
  (dgGluingIntervalUncurryHomotopyInverseMap_evaluate
    (dgGluingHomDerivedCompositionUncurriedHomotopy R C D M X Y)
    (dgGluingHomDerivedCompositionUncurriedHomotopy_source R C D M X Y)
    (dgGluingHomDerivedCompositionUncurriedHomotopy_target R C D M X Y)).trans
      (dgGluingHomDerivedCompositionUncurriedHomotopy_h R C D M X Y)

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
