module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Comparison.HomTargetInputStrictComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.HomComplexes.Models.HomTargetInputHomotopies
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.HomComplexes.Models.HomTargetCoefficientInputPathLegs
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.HomComplexes.Models.HomTargetInputPathPoints
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.HomComplexes.Models.HomTargetDiagonalBoundaryFilling
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.HomComplexes.Models.HomotopyTriangleFillingSquare
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Comparison.HomotopyInverseTransport
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory DifferentialGraded SSet KST.SConstruction
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R]
  (C D E : Type (max (u + 1) v)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
  (p : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E) (q : _root_.SerrePositivity.DifferentialGraded.DGFunctor R D E)
  (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D (dgHomGluingBimodule R C D E p q))
local notation "P" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetHomParameter R C D E p q X Y
attribute [local irreducible] dgHomGluingBimodule

def dgGluingHomTargetInputPathSquare :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingBoundaryFillingPathSquare
    (l := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLastDiagonalHomotopy R C D E p q X Y)
    (r := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCoefficientDiagonalHomotopy R C D E p q X Y)
    (d := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetFirstDiagonalHomotopy R C D E p q X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetDiagonalComparisonBoundary_filling R C D E p q X Y).choose
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetDiagonalComparisonBoundary_filling R C D E p q X Y).choose_spec

lemma dgGluingHomTargetInputPathSquare_left :
    ((ι₀ : P ⟶ P ⊗ (Δ[1] : SSet.{max (u + 1) v})) ▷
      (Δ[1] : SSet.{max (u + 1) v})) ≫
        (dgGluingHomTargetInputPathSquare R C D E p q X Y).h =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLastInputHomotopy R C D E p q X Y).h ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLastInputDiagonal R C D E p q X Y :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingBoundaryFillingPathSquare_left
    (l := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLastDiagonalHomotopy R C D E p q X Y)
    (r := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCoefficientDiagonalHomotopy R C D E p q X Y)
    (d := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetFirstDiagonalHomotopy R C D E p q X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetDiagonalComparisonBoundary_filling R C D E p q X Y).choose
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetDiagonalComparisonBoundary_filling R C D E p q X Y).choose_spec

lemma dgGluingHomTargetInputPathSquare_right :
    ((ι₁ : P ⟶ P ⊗ (Δ[1] : SSet.{max (u + 1) v})) ▷
      (Δ[1] : SSet.{max (u + 1) v})) ≫
        (dgGluingHomTargetInputPathSquare R C D E p q X Y).h =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetFirstInputHomotopy R C D E p q X Y).h ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetFirstInputDiagonal R C D E p q X Y :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingBoundaryFillingPathSquare_right
    (l := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLastDiagonalHomotopy R C D E p q X Y)
    (r := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCoefficientDiagonalHomotopy R C D E p q X Y)
    (d := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetFirstDiagonalHomotopy R C D E p q X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetDiagonalComparisonBoundary_filling R C D E p q X Y).choose
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetDiagonalComparisonBoundary_filling R C D E p q X Y).choose_spec

def dgGluingHomTargetInputPathComparisonHomotopy :
    SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetArrowInputPathComparison R C D E p q X Y)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCoefficientInputPathComparison R C D E p q X Y) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHomotopyRetarget
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIntervalPathPullbackHomotopyOfSquare
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLastInputDiagonal R C D E p q X Y)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetFirstInputDiagonal R C D E p q X Y)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetInputPathStartHomotopy R C D E p q X Y)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetInputPathEndHomotopy R C D E p q X Y)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLastInputHomotopy R C D E p q X Y)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetFirstInputHomotopy R C D E p q X Y)
      (dgGluingHomTargetInputPathSquare R C D E p q X Y)
      (dgGluingHomTargetInputPathSquare_left R C D E p q X Y)
      (dgGluingHomTargetInputPathSquare_right R C D E p q X Y))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetInputPathStartPoint_eq R C D E p q X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetInputPathEndPoint_eq R C D E p q X Y)

def dgGluingHomTargetInputPathInverse :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCoefficientInputPathComparison_equivalence R C D E p q X Y).choose

def dgGluingHomTargetInputPathInverse_unit :
    SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetArrowInputPathComparison R C D E p q X Y ≫
      dgGluingHomTargetInputPathInverse R C D E p q X Y) (𝟙 _) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomotopyInverseTransportUnit
    (dgGluingHomTargetInputPathComparisonHomotopy R C D E p q X Y)
    (dgGluingHomTargetInputPathInverse R C D E p q X Y)
    (Classical.choose_spec
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCoefficientInputPathComparison_equivalence R C D E p q X Y)).1.some

def dgGluingHomTargetInputPathInverse_counit :
    SSet.Homotopy (dgGluingHomTargetInputPathInverse R C D E p q X Y ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetArrowInputPathComparison R C D E p q X Y) (𝟙 _) := by
  letI := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetInputPathPullback_kanComplex R C D E p q X Y
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomotopyInverseTransportCounit
    (dgGluingHomTargetInputPathComparisonHomotopy R C D E p q X Y)
    (dgGluingHomTargetInputPathInverse R C D E p q X Y)
    (Classical.choose_spec
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCoefficientInputPathComparison_equivalence R C D E p q X Y)).2.some

lemma dgGluingHomTargetArrowInputPathComparison_equivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetArrowInputPathComparison R C D E p q X Y) :=
  ⟨dgGluingHomTargetInputPathInverse R C D E p q X Y,
    ⟨dgGluingHomTargetInputPathInverse_unit R C D E p q X Y⟩,
    ⟨dgGluingHomTargetInputPathInverse_counit R C D E p q X Y⟩⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
