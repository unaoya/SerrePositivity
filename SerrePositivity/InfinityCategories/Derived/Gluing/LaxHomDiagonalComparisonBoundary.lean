module
public import SerrePositivity.InfinityCategories.Derived.Gluing.LaxHomDiagonalDeformations
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomotopyTriangleBoundary

/-! 元の共通対角からの二変形と、同じ係数 path の整合性を問う実三角形境界。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalClosed DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

def dgGluingLaxHomDiagonalComparisonBoundary (X Y : DGGluingObject R C D M) :=
  dgGluingHomotopyTriangleBoundary
    (dgGluingLaxHomLastDiagonalHomotopy R C D M X Y)
    (dgGluingHomDerivedCompositionDiagonalHomotopy R C D M X Y)
    (dgGluingLaxHomFirstDiagonalHomotopy R C D M X Y)

lemma dgGluingLaxHomDiagonalComparisonBoundary_zero (X Y : DGGluingObject R C D M) :
    boundary.ι (0 : Fin 3) ≫ dgGluingLaxHomDiagonalComparisonBoundary R C D M X Y =
      curry (dgGluingHomDerivedCompositionDiagonalHomotopy R C D M X Y).h :=
  dgGluingHomotopyTriangleBoundary_zero _ _ _

lemma dgGluingLaxHomDiagonalComparisonBoundary_one (X Y : DGGluingObject R C D M) :
    boundary.ι (1 : Fin 3) ≫ dgGluingLaxHomDiagonalComparisonBoundary R C D M X Y =
      curry (dgGluingLaxHomFirstDiagonalHomotopy R C D M X Y).h :=
  dgGluingHomotopyTriangleBoundary_one _ _ _

lemma dgGluingLaxHomDiagonalComparisonBoundary_two (X Y : DGGluingObject R C D M) :
    boundary.ι (2 : Fin 3) ≫ dgGluingLaxHomDiagonalComparisonBoundary R C D M X Y =
      curry (dgGluingLaxHomLastDiagonalHomotopy R C D M X Y).h :=
  dgGluingHomotopyTriangleBoundary_two _ _ _

end SerrePositivity.InfinityCategories
