module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomDerivedCoefficientTriangles
public import SerrePositivity.InfinityCategories.Derived.Gluing.IntervalPathHomotopy
public import SerrePositivity.InfinityCategories.Derived.Gluing.IntervalUncurryHomotopy
public import SerrePositivity.InfinityCategories.F1B.HomotopyWhiskering

/-! 同じ実係数 path は、元の Hom 上の二三角形の全対角族を結ぶ実ホモトピーを与える。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

def dgGluingHomDerivedCoefficientDiagonalHomotopy (X Y : DGGluingObject R C D M) :
    SSet.Homotopy
      ((SSet.stdSimplex.δ (1 : Fin 3) ▷ _) ≫ dgGluingHomDerivedLeftCoefficientTriangle R C D M X Y)
      ((SSet.stdSimplex.δ (1 : Fin 3) ▷ _) ≫
        dgGluingHomDerivedRightCoefficientTriangle R C D M X Y) := by
  rw [dgGluingHomDerivedLeftCoefficientTriangle_diagonal R C D M X Y,
    dgGluingHomDerivedRightCoefficientTriangle_diagonal R C D M X Y]
  exact dgGluingIntervalUncurryHomotopy
    (functorHomotopyPostcomp
      (dgGluingIntervalPathHomotopy (dgGluingDerivedHomCoefficientIntervalPath R C D M X Y))
      ((dgGluingDerivedCoefficientEndpointIso R C D M X.left Y.right).inv ≫
        pinchedHomToIntervalMappingSpace _ _))

end SerrePositivity.InfinityCategories
