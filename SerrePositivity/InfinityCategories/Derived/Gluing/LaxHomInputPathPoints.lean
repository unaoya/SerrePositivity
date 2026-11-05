module
public import SerrePositivity.InfinityCategories.Derived.Gluing.IntervalPathPullbackSquare
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomotopyIntervalPathRefl
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomotopyIntervalPathValue
public import SerrePositivity.InfinityCategories.Derived.Gluing.LaxHomDiagonalDeformations
public import SerrePositivity.InfinityCategories.Derived.Gluing.LaxHomInputPathComparison
/-! # 正本の二つの入力付き path 比較を同じ三座標で回収する

概要：正本の定値対角比較と導来係数比較を、元二入力と同じ全 path による引き戻し点へ照合する。
方針：端点だけを等式で輸送し、path と入力の二射影で元比較を回収する。
規約：既存比較の射・二入力・path の代表を変更しない。
使われ方：指定境界からの実正方形ホモトピーの両端を正本比較へ接続する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : DGGluingObject R C D M)

def dgGluingLaxHomInputPathStartHomotopy : SSet.Homotopy
    (dgGluingLaxHomLastCompositionInputLift R C D M X Y ≫
      dgGluingDerivedLastCompositionInputDiagonal R C D M X Y)
    (dgGluingLaxHomFirstCompositionInputLift R C D M X Y ≫
      dgGluingDerivedFirstCompositionInputDiagonal R C D M X Y) :=
  stableHomotopyRetarget (functorHomotopyRefl (dgGluingLaxHomCommonDiagonal R C D M X Y))
    rfl (dgGluingLaxHomCommonDiagonal_first R C D M X Y)

def dgGluingLaxHomInputPathEndHomotopy : SSet.Homotopy
    (dgGluingHomDerivedLastCompositionInputLift R C D M X Y ≫
      dgGluingDerivedLastCompositionInputDiagonal R C D M X Y)
    (dgGluingHomDerivedFirstCompositionInputLift R C D M X Y ≫
      dgGluingDerivedFirstCompositionInputDiagonal R C D M X Y) :=
  stableHomotopyRetarget (dgGluingHomDerivedCompositionDiagonalHomotopy R C D M X Y)
    (dgGluingHomDerivedLastCompositionInputLift_diagonal R C D M X Y).symm
    (dgGluingHomDerivedFirstCompositionInputLift_diagonal R C D M X Y).symm

def dgGluingLaxHomInputPathStartPoint :
    (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
      (complexPinchedSpace.{u, max u v w} (dgGluingHomComplex R C D M X Y)) ⟶
        dgGluingDerivedCompositionInputPathPullback R C D M X Y :=
  dgGluingIntervalPathPullbackPoint
    (dgGluingDerivedLastCompositionInputDiagonal R C D M X Y)
    (dgGluingDerivedFirstCompositionInputDiagonal R C D M X Y)
    (dgGluingLaxHomLastCompositionInputLift R C D M X Y)
    (dgGluingLaxHomFirstCompositionInputLift R C D M X Y)
    (dgGluingLaxHomInputPathStartHomotopy R C D M X Y)

def dgGluingLaxHomInputPathEndPoint :
    (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
      (complexPinchedSpace.{u, max u v w} (dgGluingHomComplex R C D M X Y)) ⟶
        dgGluingDerivedCompositionInputPathPullback R C D M X Y :=
  dgGluingIntervalPathPullbackPoint
    (dgGluingDerivedLastCompositionInputDiagonal R C D M X Y)
    (dgGluingDerivedFirstCompositionInputDiagonal R C D M X Y)
    (dgGluingHomDerivedLastCompositionInputLift R C D M X Y)
    (dgGluingHomDerivedFirstCompositionInputLift R C D M X Y)
    (dgGluingLaxHomInputPathEndHomotopy R C D M X Y)

lemma dgGluingLaxHomInputPathStartHomotopy_h :
    (dgGluingLaxHomInputPathStartHomotopy R C D M X Y).h =
      (functorHomotopyRefl (dgGluingLaxHomCommonDiagonal R C D M X Y)).h := rfl

lemma dgGluingLaxHomInputPathStartHomotopy_path_refl :
    dgGluingHomotopyIntervalPath (dgGluingLaxHomInputPathStartHomotopy R C D M X Y) =
      dgGluingHomotopyIntervalPath
        (functorHomotopyRefl (dgGluingLaxHomCommonDiagonal R C D M X Y)) :=
  dgGluingHomotopyIntervalPath_eq_of_h_eq _ _
    (dgGluingLaxHomInputPathStartHomotopy_h R C D M X Y)

lemma dgGluingLaxHomInputPathStartHomotopy_path_constant :
    dgGluingHomotopyIntervalPath (dgGluingLaxHomInputPathStartHomotopy R C D M X Y) =
      dgGluingLaxHomCommonDiagonal R C D M X Y ≫ dgGluingConstantIntervalPath _ :=
  (dgGluingLaxHomInputPathStartHomotopy_path_refl R C D M X Y).trans
    (dgGluingHomotopyIntervalPath_refl (dgGluingLaxHomCommonDiagonal R C D M X Y))

lemma dgGluingLaxHomInputPathStartHomotopy_path_coordinate :
    dgGluingHomotopyIntervalPath (dgGluingLaxHomInputPathStartHomotopy R C D M X Y) =
      dgGluingLaxHomInputPathComparison R C D M X Y ≫ pullback.fst _ _ := by
  rw [dgGluingLaxHomInputPathStartHomotopy_path_constant R C D M X Y,
    dgGluingLaxHomCommonDiagonal, Category.assoc]
  exact (dgGluingLaxHomInputPathComparison_path R C D M X Y).symm

lemma dgGluingLaxHomInputPathStartPoint_eq :
    dgGluingLaxHomInputPathStartPoint R C D M X Y =
      dgGluingLaxHomInputPathComparison R C D M X Y := by
  exact dgGluingIntervalPathPullbackPoint_eq_of_coordinates
    (dgGluingDerivedLastCompositionInputDiagonal R C D M X Y)
    (dgGluingDerivedFirstCompositionInputDiagonal R C D M X Y)
    (dgGluingLaxHomLastCompositionInputLift R C D M X Y)
    (dgGluingLaxHomFirstCompositionInputLift R C D M X Y)
    (dgGluingLaxHomInputPathStartHomotopy R C D M X Y)
    (dgGluingLaxHomInputPathComparison R C D M X Y)
    (dgGluingLaxHomInputPathStartHomotopy_path_coordinate R C D M X Y)
    (dgGluingLaxHomInputPathComparison_compositions R C D M X Y).symm

lemma dgGluingLaxHomInputPathEndPoint_eq :
    dgGluingLaxHomInputPathEndPoint R C D M X Y =
      dgGluingHomDerivedCompositionInputPathComparison R C D M X Y := by
  exact dgGluingIntervalPathPullbackPoint_eq_of_coordinates
    (dgGluingDerivedLastCompositionInputDiagonal R C D M X Y)
    (dgGluingDerivedFirstCompositionInputDiagonal R C D M X Y)
    (dgGluingHomDerivedLastCompositionInputLift R C D M X Y)
    (dgGluingHomDerivedFirstCompositionInputLift R C D M X Y)
    (dgGluingLaxHomInputPathEndHomotopy R C D M X Y)
    (dgGluingHomDerivedCompositionInputPathComparison R C D M X Y)
    (dgGluingHomDerivedCompositionInputPathComparison_path R C D M X Y).symm
    (dgGluingHomDerivedCompositionInputPathComparison_compositions R C D M X Y).symm
end SerrePositivity.InfinityCategories
