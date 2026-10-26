module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetInputStrictComparison
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetInputHomotopies
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetCoefficientInputPathLegs
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomotopyTriangleBoundary
/-!
概要：元終域の指定共通対角と係数対角 path を、同じ実三角形境界にする。
方針：元入力固定の二変形を実対角へ送り、係数側の全 path と貼る。
規約：指定三辺を変えない。充填は次工程。使われ方：実 lax Hom 比較の逆の輸送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded DGNerve SSet KST.SConstruction
variable (R : Type u) [CommRing R]
  (C D E : Type (max (u + 1) v)) [DGCategory R C] [Small.{u} C]
  [DGCategory R D] [DGCategory R E] [Small.{u} E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)
  (X Y : DGGluingObject R C D (dgHomGluingBimodule R C D E p q))
attribute [local irreducible] dgHomGluingBimodule

def dgGluingHomTargetCommonDiagonal :=
  dgGluingHomTargetArrowLastInputLift R C D E p q X Y ≫
    dgGluingHomTargetLastInputDiagonal R C D E p q X Y

def dgGluingHomTargetLastDiagonalHomotopy :
    SSet.Homotopy (dgGluingHomTargetCommonDiagonal R C D E p q X Y)
      (dgGluingHomTargetStandardLastInputLift R C D E p q X Y ≫
        dgGluingHomTargetLastInputDiagonal R C D E p q X Y) :=
  functorHomotopyPostcomp (dgGluingHomTargetLastInputHomotopy R C D E p q X Y)
    (dgGluingHomTargetLastInputDiagonal R C D E p q X Y)

def dgGluingHomTargetFirstDiagonalHomotopy :
    SSet.Homotopy (dgGluingHomTargetCommonDiagonal R C D E p q X Y)
      (dgGluingHomTargetStandardFirstInputLift R C D E p q X Y ≫
        dgGluingHomTargetFirstInputDiagonal R C D E p q X Y) :=
  stableHomotopyRetarget
    (functorHomotopyPostcomp (dgGluingHomTargetFirstInputHomotopy R C D E p q X Y)
      (dgGluingHomTargetFirstInputDiagonal R C D E p q X Y))
    (dgGluingHomTargetArrowInputLift_diagonals R C D E p q X Y).symm rfl

def dgGluingHomTargetDiagonalComparisonBoundary :=
  dgGluingHomotopyTriangleBoundary
    (dgGluingHomTargetLastDiagonalHomotopy R C D E p q X Y)
    (dgGluingHomTargetCoefficientDiagonalHomotopy R C D E p q X Y)
    (dgGluingHomTargetFirstDiagonalHomotopy R C D E p q X Y)

end SerrePositivity.InfinityCategories
