module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightZeroTarget
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightBasePath
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroBaseChangeWitness

/-!
概要：元の指定右経路による class 比較を零底の共通標的へ送り、元の共通底へ相対化する。
方針：元の恒等係数射を後合成し、証明済みの零射影の定数式で平方零経路を持ち上げる。
規約：元の非正次数共通源と準同型射影を保持。使われ方：標準 class の間の橋渡し。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (postnikovFunctor R 1)) i m hi)
  (d : PostnikovCommonLayerInverse R f c)

abbrev postnikovCommonRightZeroPathLeft :=
  (cellPathNonpositiveComparison R (postnikovCommonRightBase R f c d) ≫
    postnikovCellClass R (B.obj i).obj 1 (by omega)) ≫
      postnikovClassToZeroBase R (B.obj i).obj 1 (by omega) 1

abbrev postnikovCommonRightZeroPathRight :=
  (cellPathNonpositiveComparison R (postnikovCommonRightDenBase R f c d) ≫
    postnikovCellClass R (B.obj i).obj 1 (by omega)) ≫
      postnikovClassToZeroBase R (B.obj i).obj 1 (by omega) 1

def postnikovCommonRightZeroPathWitness : Path.Witness R
    (postnikovCommonRightZeroPathLeft R f c d) (postnikovCommonRightZeroPathRight R f c d) :=
  (postnikovCommonRightCellClassWitness R f c d).postcomp
    (postnikovClassToZeroBase R (B.obj i).obj 1 (by omega) 1)

lemma postnikovCommonRightZeroPathWitness_projection :
    (postnikovCommonRightZeroPathWitness R f c d).hom ≫ Path.map R (SquareZero.projection _ _) =
    (postnikovCommonRightCellProjection R f c d ≫ postnikovCommonRightZeroBase R f c d) ≫
      Path.diagonal R (postnikov R (B.obj i).obj 0) := by
  change ((postnikovCommonRightCellClassWitness R f c d).hom ≫
    Path.map R (postnikovClassToZeroBase R (B.obj i).obj 1 (by omega) 1)) ≫ Path.map R _ = _
  rw [Category.assoc, ← Path.map_comp, postnikovClassToZeroBase_projection]
  exact (postnikovCommonRightCellClassWitness_zero R f c d).trans
    (congrArg (fun t => t ≫ Path.diagonal R (postnikov R (B.obj i).obj 0))
      (congrArg (fun t => postnikovCommonRightCellProjection R f c d ≫ t)
        (postnikovCommonRightZeroBase_num R f c d).symm))

lemma postnikovCommonRightZeroPathLeft_projection : postnikovCommonRightZeroPathLeft R f c d ≫
    SquareZero.projection _ _ =
      postnikovCommonRightCellProjection R f c d ≫ postnikovCommonRightZeroBase R f c d := by
  simp only [postnikovCommonRightZeroPathLeft, Category.assoc]
  rw [postnikovClassToZeroBase_projection,
    reassoc_of% (postnikovCellClass_projection R (B.obj i).obj 1 (by omega)),
    reassoc_of% (cellPathNonpositiveComparison_projection R (postnikovCommonRightBase R f c d)),
    postnikovCommonRightZeroBase_num]
  rfl

lemma postnikovCommonRightZeroPathRight_projection : postnikovCommonRightZeroPathRight R f c d ≫
    SquareZero.projection _ _ =
      postnikovCommonRightCellProjection R f c d ≫ postnikovCommonRightZeroBase R f c d := by
  simp only [postnikovCommonRightZeroPathRight, Category.assoc]
  rw [postnikovClassToZeroBase_projection,
    reassoc_of% (postnikovCellClass_projection R (B.obj i).obj 1 (by omega)),
    reassoc_of% (cellPathNonpositiveComparison_projection R (postnikovCommonRightDenBase R f c d)),
    postnikovCommonRightZeroBase_den]
  rfl

def postnikovCommonRightZeroPathSource := SquareZero.baseChangeLift
  (postnikovCommonRightZeroBase R f c d)
  (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj i).obj 1) 1)
  (postnikovCommonRightCellProjection R f c d) (postnikovCommonRightZeroPathLeft R f c d)
  (postnikovCommonRightZeroPathLeft_projection R f c d)

def postnikovCommonRightZeroPathTarget := SquareZero.baseChangeLift
  (postnikovCommonRightZeroBase R f c d)
  (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj i).obj 1) 1)
  (postnikovCommonRightCellProjection R f c d) (postnikovCommonRightZeroPathRight R f c d)
  (postnikovCommonRightZeroPathRight_projection R f c d)

def postnikovCommonRightZeroRelativeWitness : Path.Witness R
    (postnikovCommonRightZeroPathSource R f c d) (postnikovCommonRightZeroPathTarget R f c d) :=
  SquareZero.baseChangeWitness _ _ _ _ _ _ _ (postnikovCommonRightZeroPathWitness R f c d)
    (postnikovCommonRightZeroPathWitness_projection R f c d)

lemma postnikovCommonRightZeroRelativeWitness_projection :
    (postnikovCommonRightZeroRelativeWitness R f c d).hom ≫ Path.map R (SquareZero.projection _ _) =
      postnikovCommonRightCellProjection R f c d ≫ Path.diagonal R (postnikovCommonClassBase R f c d) :=
  SquareZero.baseChangeWitness_relative _ _ _ _ _ _ _ _ _

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
