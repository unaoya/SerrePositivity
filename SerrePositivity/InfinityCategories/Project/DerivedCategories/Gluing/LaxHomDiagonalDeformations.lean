module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.LaxHomTriangleHomotopyBoundaries
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.LaxHomInputStrictComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomotopyIntervalPath
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering

/-! 元の共通対角から係数模型の左右対角への同じ全変形と、二つの実 path。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

def dgGluingLaxHomCommonDiagonal (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomLastCompositionInputLift R C D M X Y ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedLastCompositionInputDiagonal R C D M X Y

lemma dgGluingLaxHomCommonDiagonal_first (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    dgGluingLaxHomCommonDiagonal R C D M X Y =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomFirstCompositionInputLift R C D M X Y ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedFirstCompositionInputDiagonal R C D M X Y :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomCompositionInputLift_diagonals R C D M X Y

def dgGluingLaxHomLastDiagonalHomotopy (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    SSet.Homotopy (dgGluingLaxHomCommonDiagonal R C D M X Y)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedLastCompositionDiagonal R C D M X Y) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHomotopyRetarget
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomLastInputHomotopy R C D M X Y)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedLastCompositionInputDiagonal R C D M X Y)) rfl
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedLastCompositionInputLift_diagonal R C D M X Y)

def dgGluingLaxHomFirstDiagonalHomotopy (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    SSet.Homotopy (dgGluingLaxHomCommonDiagonal R C D M X Y)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedFirstCompositionDiagonal R C D M X Y) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHomotopyRetarget
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomFirstInputHomotopy R C D M X Y)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedFirstCompositionInputDiagonal R C D M X Y))
    (dgGluingLaxHomCommonDiagonal_first R C D M X Y).symm
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedFirstCompositionInputLift_diagonal R C D M X Y)

lemma dgGluingLaxHomLastDiagonalHomotopy_h (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    (dgGluingLaxHomLastDiagonalHomotopy R C D M X Y).h =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomLastInputHomotopy R C D M X Y).h ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedLastCompositionInputDiagonal R C D M X Y := rfl

lemma dgGluingLaxHomFirstDiagonalHomotopy_h (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    (dgGluingLaxHomFirstDiagonalHomotopy R C D M X Y).h =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomFirstInputHomotopy R C D M X Y).h ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedFirstCompositionInputDiagonal R C D M X Y := rfl

def dgGluingLaxHomLastDiagonalDeformationPath (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomotopyIntervalPath (dgGluingLaxHomLastDiagonalHomotopy R C D M X Y)

def dgGluingLaxHomFirstDiagonalDeformationPath (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomotopyIntervalPath (dgGluingLaxHomFirstDiagonalHomotopy R C D M X Y)

lemma dgGluingLaxHomLastDiagonalDeformationPath_start (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    dgGluingLaxHomLastDiagonalDeformationPath R C D M X Y ≫
        (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalEndpointNatTrans 0).app _ = dgGluingLaxHomCommonDiagonal R C D M X Y :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomotopyIntervalPath_start _

lemma dgGluingLaxHomLastDiagonalDeformationPath_end (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    dgGluingLaxHomLastDiagonalDeformationPath R C D M X Y ≫
        (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalEndpointNatTrans 1).app _ =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedLastCompositionDiagonal R C D M X Y :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomotopyIntervalPath_end _

lemma dgGluingLaxHomFirstDiagonalDeformationPath_start (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    dgGluingLaxHomFirstDiagonalDeformationPath R C D M X Y ≫
        (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalEndpointNatTrans 0).app _ = dgGluingLaxHomCommonDiagonal R C D M X Y :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomotopyIntervalPath_start _

lemma dgGluingLaxHomFirstDiagonalDeformationPath_end (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    dgGluingLaxHomFirstDiagonalDeformationPath R C D M X Y ≫
        (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalEndpointNatTrans 1).app _ =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedFirstCompositionDiagonal R C D M X Y :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomotopyIntervalPath_end _

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
