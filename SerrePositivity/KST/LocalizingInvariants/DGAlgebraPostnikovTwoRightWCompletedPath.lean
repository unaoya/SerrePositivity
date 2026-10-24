module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoRightWZeroFollowing

/-!
概要：元の後続輸送と完成模型への復元の合成から、W 終点の native 零経路を回収する。
方針：元の実模型の両脚と全 path を計算し、動く底の終点へ照合する。
規約：完成模型射を別の候補へ置き換えない。使われ方：native 模型経路の a₁ 入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} {f : LevelHom A B}
  {j : ℕ} (d : PostnikovTwoClassInverseData R f j)

set_option quotPrecheck false
local notation "α" => SquareZeroExtension.relativeLeft
  (d.rightClassifyingLayer R) (d.rightImageClass R)
local notation "β" => SquareZeroExtension.relativeRight
  (d.rightClassifyingLayer R) (d.rightImageClass R)
local notation "K" => d.rightClassifyingLayer R
local notation "a" => d.rightImageClass R
local notation "a'" => d.fixedRightCompletedClass R
local notation "V" => postnikov R (B.obj j).obj 1
local notation "N" => postnikovShiftedLayerBimodule R (B.obj j).obj 1 (by omega) 1
local notation "C" => postnikovPerturbedClass R (B.obj j).obj 1 (by omega)
local notation "b'" => postnikovCommonClassRightDenominatorBase R f
  d.baseInverse d.layerInverse d.target_le

def rightWCompletedModel := SquareZeroExtension.transport K (d.fixedRightFollowingWitness R) ≫
  d.fixedRightCompletedRelativeToOriginalModel R

lemma rightWCompletedModel_left : d.rightWCompletedModel R ≫
    HomotopyPullbackModel.left R C (SquareZero.zeroSection V N) =
    α ≫ d.fixedRightCompletedNativeSource R := by
  simp only [rightWCompletedModel, fixedRightCompletedRelativeToOriginalModel, Category.assoc,
    d.fixedRightCompletedToOriginalModel_left R,
    reassoc_of% (SquareZeroExtension.relativeComparison_left K a')]
  exact (Category.assoc _ _ _).symm.trans (congrArg
    (fun t => t ≫ d.fixedRightCompletedNativeSource R)
    (SquareZeroExtension.transport_left K (d.fixedRightFollowingWitness R)))

lemma rightWCompletedModel_right : d.rightWCompletedModel R ≫
    HomotopyPullbackModel.right R C (SquareZero.zeroSection V N) = β ≫ b' := by
  simp only [rightWCompletedModel, fixedRightCompletedRelativeToOriginalModel, Category.assoc,
    d.fixedRightCompletedToOriginalModel_right R,
    reassoc_of% (SquareZeroExtension.relativeComparison_right K a')]
  exact (Category.assoc _ _ _).symm.trans (congrArg (fun t => t ≫ b')
    (SquareZeroExtension.transport_right K (d.fixedRightFollowingWitness R)))

lemma rightWCompletedModel_path : d.rightWCompletedModel R ≫
    HomotopyPullbackModel.path R C (SquareZero.zeroSection V N) =
    (SquareZeroExtension.transport K (d.fixedRightFollowingWitness R) ≫
      SquareZeroExtension.relativePath K a') ≫ Path.map R (d.rightDenominatorClassRestore R) := by
  simp only [rightWCompletedModel, fixedRightCompletedRelativeToOriginalModel, Category.assoc,
    d.fixedRightCompletedToOriginalModel_path R,
    reassoc_of% (SquareZeroExtension.relativeComparison_path K a')]

lemma rightDenominatorClassRestore_projection : d.rightDenominatorClassRestore R ≫
    SquareZero.projection V N = SquareZero.projection (d.classBase R) K ≫ b' :=
  SquareZero.coefficientRestore_projection _ _ _

lemma fixedRightCompletedClass_projection : a' ≫ SquareZero.projection (d.classBase R) K =
    d.classProjection R := (d.fixedRightCompletedWitness R).target_projection

lemma rightWCompletedModel_path_base : (d.rightWCompletedModel R ≫
    HomotopyPullbackModel.path R C (SquareZero.zeroSection V N)) ≫
      Path.map R (SquareZero.projection V N) = (β ≫ b') ≫ Path.diagonal R V := by
  rw [d.rightWCompletedModel_path R, Category.assoc, ← Path.map_comp,
    d.rightDenominatorClassRestore_projection R, Path.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% (SquareZeroExtension.relativePath_base K a')]
  simp only [Category.assoc, Path.diagonal_naturality]
  rw [reassoc_of% (d.fixedRightCompletedClass_projection R)]
  have hL : SquareZeroExtension.transport K (d.fixedRightFollowingWitness R) ≫
      SquareZeroExtension.relativeLeft K a' = α :=
    SquareZeroExtension.transport_left K (d.fixedRightFollowingWitness R)
  rw [reassoc_of% hL, ← reassoc_of% (d.rightImageRelativeRight R)]

def rightWCompletedNativePath : Path.Witness R
    ((α ≫ d.fixedRightCompletedNativeSource R) ≫ C)
    ((d.rightWBasePath R ≫ Path.target R V) ≫ SquareZero.zeroSection V N) where
  hom := d.rightWCompletedModel R ≫ HomotopyPullbackModel.path R C (SquareZero.zeroSection V N)
  source_eq := by
    rw [Category.assoc, HomotopyPullbackModel.path_source, ← Category.assoc,
      d.rightWCompletedModel_left R]
  target_eq := by
    rw [Category.assoc, HomotopyPullbackModel.path_target, ← Category.assoc,
      d.rightWCompletedModel_right R, d.rightWBasePath_target R]

lemma rightWCompletedNativePath_projection : (d.rightWCompletedNativePath R).hom ≫
    Path.map R (SquareZero.projection V N) =
      (d.rightWBasePath R ≫ Path.target R V) ≫ Path.diagonal R V := by
  exact (d.rightWCompletedModel_path_base R).trans
    (congrArg (fun t => t ≫ Path.diagonal R V) (d.rightWBasePath_target R).symm)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
