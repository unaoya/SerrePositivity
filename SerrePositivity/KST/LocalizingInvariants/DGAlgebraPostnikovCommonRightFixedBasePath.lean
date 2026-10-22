module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightZeroPath
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraCellPathNonpositiveFixed

/-!
概要：元の共通源と両 class を保ち、c の指定右経路の全射影を固定する class 経路。
方針：両端固定の新しい cell 持ち上げを既存の非正次数源へ移し、実 class を後合成する。
規約：旧 class 経路との一致は仮定しない。使われ方：Γ の右三角形の指定底経路。
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

def postnikovCommonRightFixedCellClassWitness : Path.Witness R
    (cellPathNonpositiveComparison R (postnikovCommonRightBase R f c d) ≫
      postnikovCellClass R (B.obj i).obj 1 (by omega))
    (cellPathNonpositiveComparison R (postnikovCommonRightDenBase R f c d) ≫
      postnikovCellClass R (B.obj i).obj 1 (by omega)) :=
  (cellPathNonpositiveFixedWitness R (postnikovCommonRightBasePath R f c d)).postcomp
    (postnikovCellClass R (B.obj i).obj 1 (by omega))

lemma postnikovCommonRightFixedCellClassWitness_projection :
    (postnikovCommonRightFixedCellClassWitness R f c d).hom ≫
      Path.map R (SquareZero.projection (postnikov R (B.obj i).obj 1)
        (postnikovShiftedLayerBimodule R (B.obj i).obj 1 (by omega) 1)) =
    postnikovCommonRightCellProjection R f c d ≫ (postnikovCommonRightBasePath R f c d).hom := by
  change ((cellPathNonpositiveFixedWitness R (postnikovCommonRightBasePath R f c d)).hom ≫
    Path.map R (postnikovCellClass R (B.obj i).obj 1 (by omega))) ≫ _ = _
  rw [Category.assoc, ← Path.map_comp, postnikovCellClass_projection,
    cellPathNonpositiveFixedWitness_map]
  rfl

lemma postnikovCommonRightFixedCellClassWitness_zero :
    (postnikovCommonRightFixedCellClassWitness R f c d).hom ≫
      Path.map R (SquareZero.projection (postnikov R (B.obj i).obj 1)
        (postnikovShiftedLayerBimodule R (B.obj i).obj 1 (by omega) 1) ≫
          postnikovTransition R (B.obj i).obj 1 0 (by omega)) =
    (postnikovCommonRightCellProjection R f c d ≫ postnikovCommonRightBase R f c d ≫
      postnikovTransition R (B.obj i).obj 1 0 (by omega)) ≫
        Path.diagonal R (postnikov R (B.obj i).obj 0) := by
  rw [Path.map_comp, ← Category.assoc, postnikovCommonRightFixedCellClassWitness_projection,
    Category.assoc, postnikovCommonRightBasePath_zero]
  simp only [Category.assoc]

def postnikovCommonRightFixedZeroPathWitness : Path.Witness R
    (postnikovCommonRightZeroPathLeft R f c d) (postnikovCommonRightZeroPathRight R f c d) :=
  (postnikovCommonRightFixedCellClassWitness R f c d).postcomp
    (postnikovClassToZeroBase R (B.obj i).obj 1 (by omega) 1)

lemma postnikovCommonRightFixedZeroPathWitness_projection :
    (postnikovCommonRightFixedZeroPathWitness R f c d).hom ≫
      Path.map R (SquareZero.projection _ _) =
    (postnikovCommonRightCellProjection R f c d ≫ postnikovCommonRightZeroBase R f c d) ≫
      Path.diagonal R (postnikov R (B.obj i).obj 0) := by
  change ((postnikovCommonRightFixedCellClassWitness R f c d).hom ≫
    Path.map R (postnikovClassToZeroBase R (B.obj i).obj 1 (by omega) 1)) ≫ _ = _
  rw [Category.assoc, ← Path.map_comp, postnikovClassToZeroBase_projection]
  exact (postnikovCommonRightFixedCellClassWitness_zero R f c d).trans
    (congrArg (fun t => t ≫ Path.diagonal R (postnikov R (B.obj i).obj 0))
      (congrArg (fun t => postnikovCommonRightCellProjection R f c d ≫ t)
        (postnikovCommonRightZeroBase_num R f c d).symm))

def postnikovCommonRightFixedZeroRelativeWitness : Path.Witness R
    (postnikovCommonRightZeroPathSource R f c d) (postnikovCommonRightZeroPathTarget R f c d) :=
  SquareZero.baseChangeWitness _ _ _ _ _
    (postnikovCommonRightZeroPathLeft_projection R f c d)
    (postnikovCommonRightZeroPathRight_projection R f c d)
    (postnikovCommonRightFixedZeroPathWitness R f c d)
    (postnikovCommonRightFixedZeroPathWitness_projection R f c d)

lemma postnikovCommonRightFixedZeroRelativeWitness_projection :
    (postnikovCommonRightFixedZeroRelativeWitness R f c d).hom ≫
      Path.map R (SquareZero.projection _ _) =
    postnikovCommonRightCellProjection R f c d ≫
      Path.diagonal R (postnikovCommonClassBase R f c d) :=
  SquareZero.baseChangeWitness_relative _ _ _ _ _ _ _ _ _

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
