module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomotopyPullbackConeNaturality
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCellHomotopyPullback

/-!
概要：元の Postnikov class の零化データを、全乗法的経路を保つ実模型で表現する。
方針：平方零微分摂動と cell derivation の cospan に、全経路付き錐の同値を適用する。
規約：元の上段からの比較は二脚と定数経路を保持する。導来写像空間との比較は別工程。
使われ方：隣接 Postnikov 拡大の普遍性と、cell class での具体的零化の回収。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open HomotopyPullbackModel
variable (R : Type u) [CommRing R] (B : Mon (Complex R)) [B.X.IsStrictlyLE 0]
  (n : ℤ) (hn : 0 ≤ n) (W : Mon (Complex R))

abbrev PostnikovPerturbedPathCone := PathCone R (postnikovPerturbedClass R B n hn)
  (SquareZero.zeroSection (postnikov R B n) (postnikovShiftedLayerBimodule R B n hn 1)) W

abbrev PostnikovCellPathCone := PathCone R (postnikovCellClass R B n hn)
  (SquareZero.zeroSection (postnikov R B n) (postnikovShiftedLayerBimodule R B n hn 1)) W

def postnikovPerturbedPathConeEquiv :
    (W ⟶ algebra R (postnikovPerturbedClass R B n hn)
      (SquareZero.zeroSection (postnikov R B n) (postnikovShiftedLayerBimodule R B n hn 1))) ≃
        PostnikovPerturbedPathCone R B n hn W := homPathConeEquiv R _ _

def postnikovCellPathConeEquiv :
    (W ⟶ algebra R (postnikovCellClass R B n hn)
      (SquareZero.zeroSection (postnikov R B n) (postnikovShiftedLayerBimodule R B n hn 1))) ≃
        PostnikovCellPathCone R B n hn W := homPathConeEquiv R _ _

def postnikovCellPathConeToPerturbed (s : PostnikovCellPathCone R B n hn W) :
    PostnikovPerturbedPathCone R B n hn W where
  left := s.left ≫ postnikovCellLift R B n hn
  right := s.right
  path := s.path
  source_eq := by rw [Category.assoc]; exact s.source_eq
  target_eq := s.target_eq

lemma postnikovCellPathConeComparison (a : W ⟶ algebra R (postnikovCellClass R B n hn)
    (SquareZero.zeroSection (postnikov R B n) (postnikovShiftedLayerBimodule R B n hn 1))) :
    postnikovPerturbedPathConeEquiv R B n hn W
      (a ≫ postnikovCellHomotopyPullbackComparison R B n hn) =
    postnikovCellPathConeToPerturbed R B n hn W (postnikovCellPathConeEquiv R B n hn W a) := by
  apply PathCone.ext R _ _
  · change (a ≫ postnikovCellHomotopyPullbackComparison R B n hn) ≫ left R _ _ =
      (a ≫ left R _ _) ≫ postnikovCellLift R B n hn
    rw [Category.assoc, postnikovCellHomotopyPullbackComparison_left, Category.assoc]
  · change (a ≫ postnikovCellHomotopyPullbackComparison R B n hn) ≫ right R _ _ =
      a ≫ right R _ _
    rw [Category.assoc, postnikovCellHomotopyPullbackComparison_right]
  · change (a ≫ postnikovCellHomotopyPullbackComparison R B n hn) ≫ path R _ _ =
      a ≫ path R _ _
    rw [Category.assoc, postnikovCellHomotopyPullbackComparison_path]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
