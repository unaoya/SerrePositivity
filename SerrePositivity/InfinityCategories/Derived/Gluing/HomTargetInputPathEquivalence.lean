module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetInputStrictComparison
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetInputHomotopies
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetCoefficientInputPathLegs
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetInputPathPoints
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetDiagonalBoundaryFilling
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomotopyTriangleFillingSquare
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomotopyInverseTransport
/-!
概要：指定境界充填から元入力付き path 比較の実逆射と両往復変形を構成する。
方針：元の全入力・指定面・全区間族を保持する比較を合成する。
規約：追加の主経路仮定を置かない。使われ方：元 lax Hom 比較の逆の輸送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory DifferentialGraded DGNerve SSet KST.SConstruction
open scoped Simplicial
variable (R : Type u) [CommRing R]
  (C D E : Type (max (u + 1) v)) [DGCategory R C] [Small.{u} C]
  [DGCategory R D] [DGCategory R E] [Small.{u} E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)
  (X Y : DGGluingObject R C D (dgHomGluingBimodule R C D E p q))
local notation "P" => dgGluingHomTargetHomParameter R C D E p q X Y
attribute [local irreducible] dgHomGluingBimodule

def dgGluingHomTargetInputPathSquare :=
  dgGluingBoundaryFillingPathSquare
    (l := dgGluingHomTargetLastDiagonalHomotopy R C D E p q X Y)
    (r := dgGluingHomTargetCoefficientDiagonalHomotopy R C D E p q X Y)
    (d := dgGluingHomTargetFirstDiagonalHomotopy R C D E p q X Y)
    (dgGluingHomTargetDiagonalComparisonBoundary_filling R C D E p q X Y).choose
    (dgGluingHomTargetDiagonalComparisonBoundary_filling R C D E p q X Y).choose_spec

lemma dgGluingHomTargetInputPathSquare_left :
    ((ι₀ : P ⟶ P ⊗ (Δ[1] : SSet.{max (u + 1) v})) ▷
      (Δ[1] : SSet.{max (u + 1) v})) ≫
        (dgGluingHomTargetInputPathSquare R C D E p q X Y).h =
    (dgGluingHomTargetLastInputHomotopy R C D E p q X Y).h ≫
      dgGluingHomTargetLastInputDiagonal R C D E p q X Y :=
  dgGluingBoundaryFillingPathSquare_left
    (l := dgGluingHomTargetLastDiagonalHomotopy R C D E p q X Y)
    (r := dgGluingHomTargetCoefficientDiagonalHomotopy R C D E p q X Y)
    (d := dgGluingHomTargetFirstDiagonalHomotopy R C D E p q X Y)
    (dgGluingHomTargetDiagonalComparisonBoundary_filling R C D E p q X Y).choose
    (dgGluingHomTargetDiagonalComparisonBoundary_filling R C D E p q X Y).choose_spec

lemma dgGluingHomTargetInputPathSquare_right :
    ((ι₁ : P ⟶ P ⊗ (Δ[1] : SSet.{max (u + 1) v})) ▷
      (Δ[1] : SSet.{max (u + 1) v})) ≫
        (dgGluingHomTargetInputPathSquare R C D E p q X Y).h =
    (dgGluingHomTargetFirstInputHomotopy R C D E p q X Y).h ≫
      dgGluingHomTargetFirstInputDiagonal R C D E p q X Y :=
  dgGluingBoundaryFillingPathSquare_right
    (l := dgGluingHomTargetLastDiagonalHomotopy R C D E p q X Y)
    (r := dgGluingHomTargetCoefficientDiagonalHomotopy R C D E p q X Y)
    (d := dgGluingHomTargetFirstDiagonalHomotopy R C D E p q X Y)
    (dgGluingHomTargetDiagonalComparisonBoundary_filling R C D E p q X Y).choose
    (dgGluingHomTargetDiagonalComparisonBoundary_filling R C D E p q X Y).choose_spec

def dgGluingHomTargetInputPathComparisonHomotopy :
    SSet.Homotopy (dgGluingHomTargetArrowInputPathComparison R C D E p q X Y)
      (dgGluingHomTargetCoefficientInputPathComparison R C D E p q X Y) :=
  stableHomotopyRetarget
    (dgGluingIntervalPathPullbackHomotopyOfSquare
      (dgGluingHomTargetLastInputDiagonal R C D E p q X Y)
      (dgGluingHomTargetFirstInputDiagonal R C D E p q X Y)
      (dgGluingHomTargetInputPathStartHomotopy R C D E p q X Y)
      (dgGluingHomTargetInputPathEndHomotopy R C D E p q X Y)
      (dgGluingHomTargetLastInputHomotopy R C D E p q X Y)
      (dgGluingHomTargetFirstInputHomotopy R C D E p q X Y)
      (dgGluingHomTargetInputPathSquare R C D E p q X Y)
      (dgGluingHomTargetInputPathSquare_left R C D E p q X Y)
      (dgGluingHomTargetInputPathSquare_right R C D E p q X Y))
    (dgGluingHomTargetInputPathStartPoint_eq R C D E p q X Y)
    (dgGluingHomTargetInputPathEndPoint_eq R C D E p q X Y)

def dgGluingHomTargetInputPathInverse :=
  (dgGluingHomTargetCoefficientInputPathComparison_equivalence R C D E p q X Y).choose

def dgGluingHomTargetInputPathInverse_unit :
    SSet.Homotopy (dgGluingHomTargetArrowInputPathComparison R C D E p q X Y ≫
      dgGluingHomTargetInputPathInverse R C D E p q X Y) (𝟙 _) :=
  dgGluingHomotopyInverseTransportUnit
    (dgGluingHomTargetInputPathComparisonHomotopy R C D E p q X Y)
    (dgGluingHomTargetInputPathInverse R C D E p q X Y)
    (Classical.choose_spec
      (dgGluingHomTargetCoefficientInputPathComparison_equivalence R C D E p q X Y)).1.some

def dgGluingHomTargetInputPathInverse_counit :
    SSet.Homotopy (dgGluingHomTargetInputPathInverse R C D E p q X Y ≫
      dgGluingHomTargetArrowInputPathComparison R C D E p q X Y) (𝟙 _) := by
  letI := dgGluingHomTargetInputPathPullback_kanComplex R C D E p q X Y
  exact dgGluingHomotopyInverseTransportCounit
    (dgGluingHomTargetInputPathComparisonHomotopy R C D E p q X Y)
    (dgGluingHomTargetInputPathInverse R C D E p q X Y)
    (Classical.choose_spec
      (dgGluingHomTargetCoefficientInputPathComparison_equivalence R C D E p q X Y)).2.some

lemma dgGluingHomTargetArrowInputPathComparison_equivalence :
    IsSimplicialHomotopyEquivalence (dgGluingHomTargetArrowInputPathComparison R C D E p q X Y) :=
  ⟨dgGluingHomTargetInputPathInverse R C D E p q X Y,
    ⟨dgGluingHomTargetInputPathInverse_unit R C D E p q X Y⟩,
    ⟨dgGluingHomTargetInputPathInverse_counit R C D E p q X Y⟩⟩

end SerrePositivity.InfinityCategories
