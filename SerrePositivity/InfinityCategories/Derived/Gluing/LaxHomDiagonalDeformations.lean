module
public import SerrePositivity.InfinityCategories.Derived.Gluing.LaxHomTriangleHomotopyBoundaries
public import SerrePositivity.InfinityCategories.Derived.Gluing.LaxHomInputStrictComparison
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomotopyIntervalPath
public import SerrePositivity.InfinityCategories.F1B.HomotopyWhiskering

/-! 元の共通対角から係数模型の左右対角への同じ全変形と、二つの実 path。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

def dgGluingLaxHomCommonDiagonal (X Y : DGGluingObject R C D M) :=
  dgGluingLaxHomLastCompositionInputLift R C D M X Y ≫
    dgGluingDerivedLastCompositionInputDiagonal R C D M X Y

lemma dgGluingLaxHomCommonDiagonal_first (X Y : DGGluingObject R C D M) :
    dgGluingLaxHomCommonDiagonal R C D M X Y =
      dgGluingLaxHomFirstCompositionInputLift R C D M X Y ≫
        dgGluingDerivedFirstCompositionInputDiagonal R C D M X Y :=
  dgGluingLaxHomCompositionInputLift_diagonals R C D M X Y

def dgGluingLaxHomLastDiagonalHomotopy (X Y : DGGluingObject R C D M) :
    SSet.Homotopy (dgGluingLaxHomCommonDiagonal R C D M X Y)
      (dgGluingHomDerivedLastCompositionDiagonal R C D M X Y) :=
  stableHomotopyRetarget
    (functorHomotopyPostcomp (dgGluingLaxHomLastInputHomotopy R C D M X Y)
      (dgGluingDerivedLastCompositionInputDiagonal R C D M X Y)) rfl
    (dgGluingHomDerivedLastCompositionInputLift_diagonal R C D M X Y)

def dgGluingLaxHomFirstDiagonalHomotopy (X Y : DGGluingObject R C D M) :
    SSet.Homotopy (dgGluingLaxHomCommonDiagonal R C D M X Y)
      (dgGluingHomDerivedFirstCompositionDiagonal R C D M X Y) :=
  stableHomotopyRetarget
    (functorHomotopyPostcomp (dgGluingLaxHomFirstInputHomotopy R C D M X Y)
      (dgGluingDerivedFirstCompositionInputDiagonal R C D M X Y))
    (dgGluingLaxHomCommonDiagonal_first R C D M X Y).symm
    (dgGluingHomDerivedFirstCompositionInputLift_diagonal R C D M X Y)

lemma dgGluingLaxHomLastDiagonalHomotopy_h (X Y : DGGluingObject R C D M) :
    (dgGluingLaxHomLastDiagonalHomotopy R C D M X Y).h =
      (dgGluingLaxHomLastInputHomotopy R C D M X Y).h ≫
        dgGluingDerivedLastCompositionInputDiagonal R C D M X Y := rfl

lemma dgGluingLaxHomFirstDiagonalHomotopy_h (X Y : DGGluingObject R C D M) :
    (dgGluingLaxHomFirstDiagonalHomotopy R C D M X Y).h =
      (dgGluingLaxHomFirstInputHomotopy R C D M X Y).h ≫
        dgGluingDerivedFirstCompositionInputDiagonal R C D M X Y := rfl

def dgGluingLaxHomLastDiagonalDeformationPath (X Y : DGGluingObject R C D M) :=
  dgGluingHomotopyIntervalPath (dgGluingLaxHomLastDiagonalHomotopy R C D M X Y)

def dgGluingLaxHomFirstDiagonalDeformationPath (X Y : DGGluingObject R C D M) :=
  dgGluingHomotopyIntervalPath (dgGluingLaxHomFirstDiagonalHomotopy R C D M X Y)

lemma dgGluingLaxHomLastDiagonalDeformationPath_start (X Y : DGGluingObject R C D M) :
    dgGluingLaxHomLastDiagonalDeformationPath R C D M X Y ≫
        (F2.intervalEndpointNatTrans 0).app _ = dgGluingLaxHomCommonDiagonal R C D M X Y :=
  dgGluingHomotopyIntervalPath_start _

lemma dgGluingLaxHomLastDiagonalDeformationPath_end (X Y : DGGluingObject R C D M) :
    dgGluingLaxHomLastDiagonalDeformationPath R C D M X Y ≫
        (F2.intervalEndpointNatTrans 1).app _ =
      dgGluingHomDerivedLastCompositionDiagonal R C D M X Y :=
  dgGluingHomotopyIntervalPath_end _

lemma dgGluingLaxHomFirstDiagonalDeformationPath_start (X Y : DGGluingObject R C D M) :
    dgGluingLaxHomFirstDiagonalDeformationPath R C D M X Y ≫
        (F2.intervalEndpointNatTrans 0).app _ = dgGluingLaxHomCommonDiagonal R C D M X Y :=
  dgGluingHomotopyIntervalPath_start _

lemma dgGluingLaxHomFirstDiagonalDeformationPath_end (X Y : DGGluingObject R C D M) :
    dgGluingLaxHomFirstDiagonalDeformationPath R C D M X Y ≫
        (F2.intervalEndpointNatTrans 1).app _ =
      dgGluingHomDerivedFirstCompositionDiagonal R C D M X Y :=
  dgGluingHomotopyIntervalPath_end _

end SerrePositivity.InfinityCategories
