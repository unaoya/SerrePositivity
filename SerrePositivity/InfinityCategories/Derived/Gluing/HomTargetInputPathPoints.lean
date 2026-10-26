module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetDiagonalComparisonBoundary
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetInputStrictComparison
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetInputHomotopies
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetCoefficientInputPathLegs
public import SerrePositivity.InfinityCategories.Derived.Gluing.LaxHomInputPathPoints
/-!
概要：元二入力と全 path を保持して指定比較の二端を引き戻し点へ同定する。
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

lemma dgGluingHomTargetArrowInputPathComparison_path :
    dgGluingHomTargetArrowInputPathComparison R C D E p q X Y ≫
      dgGluingHomTargetInputPathProjection R C D E p q X Y =
    dgGluingHomTargetArrowLastInputLift R C D E p q X Y ≫
      dgGluingHomTargetLastInputDiagonal R C D E p q X Y ≫
        dgGluingConstantIntervalPath _ := by
  rw [dgGluingHomTargetArrowInputPathComparison, dgGluingHomTargetInputPathProjection,
    dgGluingHomTargetInputStrictPathComparison, Category.assoc,
    dgGluingStrictPathPullbackMap_path]
  simp only [dgGluingHomTargetArrowInputStrictComparison,
    pullback.lift_fst_assoc, Category.assoc]

lemma dgGluingHomTargetArrowInputPathComparison_inputs :
    dgGluingHomTargetArrowInputPathComparison R C D E p q X Y ≫
      dgGluingHomTargetInputPairProjection R C D E p q X Y =
    lift (dgGluingHomTargetArrowLastInputLift R C D E p q X Y)
      (dgGluingHomTargetArrowFirstInputLift R C D E p q X Y) := by
  rw [dgGluingHomTargetArrowInputPathComparison, dgGluingHomTargetInputPairProjection,
    dgGluingHomTargetInputStrictPathComparison, Category.assoc,
    dgGluingStrictPathPullbackMap_inputs]
  apply CartesianMonoidalCategory.hom_ext <;>
    simp only [dgGluingHomTargetArrowInputStrictComparison, Category.assoc,
      lift_fst, lift_snd, lift_fst_assoc, lift_snd_assoc,
      pullback.lift_fst, pullback.lift_snd]

def dgGluingHomTargetInputPathStartHomotopy : SSet.Homotopy
    (dgGluingHomTargetArrowLastInputLift R C D E p q X Y ≫
      dgGluingHomTargetLastInputDiagonal R C D E p q X Y)
    (dgGluingHomTargetArrowFirstInputLift R C D E p q X Y ≫
      dgGluingHomTargetFirstInputDiagonal R C D E p q X Y) :=
  stableHomotopyRetarget (functorHomotopyRefl (dgGluingHomTargetCommonDiagonal R C D E p q X Y))
    rfl (dgGluingHomTargetArrowInputLift_diagonals R C D E p q X Y)

def dgGluingHomTargetInputPathEndHomotopy : SSet.Homotopy
    (dgGluingHomTargetStandardLastInputLift R C D E p q X Y ≫
      dgGluingHomTargetLastInputDiagonal R C D E p q X Y)
    (dgGluingHomTargetStandardFirstInputLift R C D E p q X Y ≫
      dgGluingHomTargetFirstInputDiagonal R C D E p q X Y) :=
  stableHomotopyRetarget (dgGluingHomTargetCoefficientDiagonalHomotopy R C D E p q X Y)
    rfl rfl

def dgGluingHomTargetInputPathStartPoint :
    P ⟶
        dgGluingHomTargetInputPathPullback R C D E p q X Y :=
  dgGluingIntervalPathPullbackPoint
    (dgGluingHomTargetLastInputDiagonal R C D E p q X Y)
    (dgGluingHomTargetFirstInputDiagonal R C D E p q X Y)
    (dgGluingHomTargetArrowLastInputLift R C D E p q X Y)
    (dgGluingHomTargetArrowFirstInputLift R C D E p q X Y)
    (dgGluingHomTargetInputPathStartHomotopy R C D E p q X Y)

def dgGluingHomTargetInputPathEndPoint :
    P ⟶
        dgGluingHomTargetInputPathPullback R C D E p q X Y :=
  dgGluingIntervalPathPullbackPoint
    (dgGluingHomTargetLastInputDiagonal R C D E p q X Y)
    (dgGluingHomTargetFirstInputDiagonal R C D E p q X Y)
    (dgGluingHomTargetStandardLastInputLift R C D E p q X Y)
    (dgGluingHomTargetStandardFirstInputLift R C D E p q X Y)
    (dgGluingHomTargetInputPathEndHomotopy R C D E p q X Y)

lemma dgGluingHomTargetInputPathStartHomotopy_h :
    (dgGluingHomTargetInputPathStartHomotopy R C D E p q X Y).h =
      (functorHomotopyRefl (dgGluingHomTargetCommonDiagonal R C D E p q X Y)).h := rfl

lemma dgGluingHomTargetInputPathStartHomotopy_path_refl :
    dgGluingHomotopyIntervalPath (dgGluingHomTargetInputPathStartHomotopy R C D E p q X Y) =
      dgGluingHomotopyIntervalPath
        (functorHomotopyRefl (dgGluingHomTargetCommonDiagonal R C D E p q X Y)) :=
  dgGluingHomotopyIntervalPath_eq_of_h_eq _ _
    (dgGluingHomTargetInputPathStartHomotopy_h R C D E p q X Y)

lemma dgGluingHomTargetInputPathStartHomotopy_path_constant :
    dgGluingHomotopyIntervalPath (dgGluingHomTargetInputPathStartHomotopy R C D E p q X Y) =
      dgGluingHomTargetCommonDiagonal R C D E p q X Y ≫ dgGluingConstantIntervalPath _ :=
  (dgGluingHomTargetInputPathStartHomotopy_path_refl R C D E p q X Y).trans
    (dgGluingHomotopyIntervalPath_refl (dgGluingHomTargetCommonDiagonal R C D E p q X Y))

lemma dgGluingHomTargetInputPathStartHomotopy_path_coordinate :
    dgGluingHomotopyIntervalPath (dgGluingHomTargetInputPathStartHomotopy R C D E p q X Y) =
      dgGluingHomTargetArrowInputPathComparison R C D E p q X Y ≫
        dgGluingHomTargetInputPathProjection R C D E p q X Y := by
  rw [dgGluingHomTargetInputPathStartHomotopy_path_constant R C D E p q X Y,
    dgGluingHomTargetCommonDiagonal, Category.assoc]
  exact (dgGluingHomTargetArrowInputPathComparison_path R C D E p q X Y).symm

lemma dgGluingHomTargetInputPathStartPoint_eq :
    dgGluingHomTargetInputPathStartPoint R C D E p q X Y =
      dgGluingHomTargetArrowInputPathComparison R C D E p q X Y := by
  exact dgGluingIntervalPathPullbackPoint_eq_of_coordinates
    (dgGluingHomTargetLastInputDiagonal R C D E p q X Y)
    (dgGluingHomTargetFirstInputDiagonal R C D E p q X Y)
    (dgGluingHomTargetArrowLastInputLift R C D E p q X Y)
    (dgGluingHomTargetArrowFirstInputLift R C D E p q X Y)
    (dgGluingHomTargetInputPathStartHomotopy R C D E p q X Y)
    (dgGluingHomTargetArrowInputPathComparison R C D E p q X Y)
    (dgGluingHomTargetInputPathStartHomotopy_path_coordinate R C D E p q X Y)
    (dgGluingHomTargetArrowInputPathComparison_inputs R C D E p q X Y).symm

lemma dgGluingHomTargetInputPathEndPoint_eq :
    dgGluingHomTargetInputPathEndPoint R C D E p q X Y =
      dgGluingHomTargetCoefficientInputPathComparison R C D E p q X Y := by
  exact dgGluingIntervalPathPullbackPoint_eq_of_coordinates
    (dgGluingHomTargetLastInputDiagonal R C D E p q X Y)
    (dgGluingHomTargetFirstInputDiagonal R C D E p q X Y)
    (dgGluingHomTargetStandardLastInputLift R C D E p q X Y)
    (dgGluingHomTargetStandardFirstInputLift R C D E p q X Y)
    (dgGluingHomTargetInputPathEndHomotopy R C D E p q X Y)
    (dgGluingHomTargetCoefficientInputPathComparison R C D E p q X Y)
    (by
      change dgGluingHomotopyIntervalPath _ = dgGluingHomTargetCoefficientDiagonalPath _ _ _ _ _ _ _ _
      unfold dgGluingHomotopyIntervalPath dgGluingHomTargetInputPathEndHomotopy
        dgGluingHomTargetCoefficientDiagonalHomotopy
      change curry ((β_ (Δ[1] : SSet.{max (u + 1) v}) P).hom ≫
        (β_ P (Δ[1] : SSet.{max (u + 1) v})).hom ≫ uncurry _) = _
      simp only [← Category.assoc, SymmetricCategory.symmetry,
        Category.id_comp, curry_uncurry])
    (dgGluingHomTargetCoefficientInputPathComparison_inputs R C D E p q X Y).symm
end SerrePositivity.InfinityCategories
