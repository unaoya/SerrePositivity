module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoFixedRightDirectRelativeInput
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroSourceModelHomotopy

/-!
概要：元の source 相対模型上の直接 B 遷移の自然性から、実模型経路を構成する。
方針：構成済みの実経路と相対 class 入力を、一定底の source 模型ホモトピーへ渡す。
規約：元の source 相対模型と Bⱼ 模型を保持。使われ方：元の直接遷移への照合。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} {f : LevelHom A B}
  {j : ℕ} (d : PostnikovTwoClassInverseData R f j)

def directSourceInitialModelMap : d.sourceRelativeModel R ⟶
    postnikovClassModel R (B.obj j).obj 1 (by omega) :=
  SquareZeroExtension.sourceModelInitialMap (directNativeLayer (B := B) (j := j) R)
    (postnikovPerturbedClass R (B.obj j).obj 1 (by omega)) (d.directRelativeBase R)
    (d.directInitialNativeWitness R)

def directSourceFinalModelMap : d.sourceRelativeModel R ⟶
    postnikovClassModel R (B.obj j).obj 1 (by omega) :=
  SquareZeroExtension.sourceModelFinalMap (directNativeLayer (B := B) (j := j) R)
    (postnikovPerturbedClass R (B.obj j).obj 1 (by omega)) (d.directRelativeBase R)
    (d.directRelativeSourcePath R) (d.directRelativeSourcePath_class_relative R)
    (d.directInitialNativeWitness R)

def directSourceModelHomotopy : Path.Witness R
    (d.directSourceInitialModelMap R) (d.directSourceFinalModelMap R) :=
  SquareZeroExtension.sourceModelHomotopy (directNativeLayer (B := B) (j := j) R)
    (postnikovPerturbedClass R (B.obj j).obj 1 (by omega)) (d.directRelativeBase R)
    (d.directRelativeSourcePath R) (d.directRelativeSourcePath_class_relative R)
    (d.directInitialNativeWitness R)

lemma directSourceInitialModelMap_left : d.directSourceInitialModelMap R ≫
    HomotopyPullbackModel.left R _ _ =
    SquareZeroExtension.relativeLeft (d.denominatorLayer R) (d.sourceClass R) ≫
      d.directNativeSource R := HomotopyPullbackModel.lift_left R _ _ _ _ _

lemma directSourceInitialModelMap_right : d.directSourceInitialModelMap R ≫
    HomotopyPullbackModel.right R _ _ = d.directRelativeBase R :=
  HomotopyPullbackModel.lift_right R _ _ _ _ _

lemma directSourceInitialModelMap_path : d.directSourceInitialModelMap R ≫
    HomotopyPullbackModel.path R _ _ = (d.directInitialNativeWitness R).hom :=
  HomotopyPullbackModel.lift_path R _ _ _ _ _

lemma directSourceModelHomotopy_left : (d.directSourceModelHomotopy R).hom ≫
    Path.map R (HomotopyPullbackModel.left R _ _) = (d.directRelativeSourcePath R).hom :=
  SquareZeroExtension.sourceModelHomotopy_left _ _ _ _ _ _

lemma directSourceModelHomotopy_right : (d.directSourceModelHomotopy R).hom ≫
    Path.map R (HomotopyPullbackModel.right R _ _) =
    d.directRelativeBase R ≫ Path.diagonal R (postnikov R (B.obj j).obj 1) :=
  SquareZeroExtension.sourceModelHomotopy_right _ _ _ _ _ _

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
