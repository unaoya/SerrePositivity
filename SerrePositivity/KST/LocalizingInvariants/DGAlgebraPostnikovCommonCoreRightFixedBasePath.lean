module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightZeroPath
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
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
open ProExcision
variable (R : Type u) [CommRing R] {n : ℤ} (hn : 0 ≤ n)
  {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (lowerFunctor R n hn)) i m hi)
  (d : PostnikovCommonLayerInverse R hn f c)

attribute [local instance] PostnikovRoofZeroSpan.refined_source_nonpositive
  PostnikovRoofZeroSpan.refined_target_nonpositive

def postnikovCommonRightFixedCellClassWitness : Path.Witness R
    (cellPathNonpositiveComparison R (postnikovCommonRightBase R hn f c d) ≫
      postnikovCellClass R (B.obj i).obj n hn)
    (cellPathNonpositiveComparison R (postnikovCommonRightDenBase R hn f c d) ≫
      postnikovCellClass R (B.obj i).obj n hn) :=
  (cellPathNonpositiveFixedWitness R (postnikovCommonRightBasePath R hn f c d)).postcomp
    (postnikovCellClass R (B.obj i).obj n hn)

lemma postnikovCommonRightFixedCellClassWitness_projection :
    (postnikovCommonRightFixedCellClassWitness R hn f c d).hom ≫
      Path.map R (SquareZero.projection (postnikov R (B.obj i).obj n)
        (postnikovShiftedLayerBimodule R (B.obj i).obj n hn 1)) =
    postnikovCommonRightCellProjection R hn f c d ≫ (postnikovCommonRightBasePath R hn f c d).hom := by
  change ((cellPathNonpositiveFixedWitness R (postnikovCommonRightBasePath R hn f c d)).hom ≫
    Path.map R (postnikovCellClass R (B.obj i).obj n hn)) ≫ _ = _
  rw [Category.assoc, ← Path.map_comp, postnikovCellClass_projection,
    cellPathNonpositiveFixedWitness_map]
  rfl

lemma postnikovCommonRightFixedCellClassWitness_zero :
    (postnikovCommonRightFixedCellClassWitness R hn f c d).hom ≫
      Path.map R (SquareZero.projection (postnikov R (B.obj i).obj n)
        (postnikovShiftedLayerBimodule R (B.obj i).obj n hn 1) ≫
          postnikovTransition R (B.obj i).obj n 0 (by omega)) =
    (postnikovCommonRightCellProjection R hn f c d ≫ postnikovCommonRightBase R hn f c d ≫
      postnikovTransition R (B.obj i).obj n 0 (by omega)) ≫
        Path.diagonal R (postnikov R (B.obj i).obj 0) := by
  rw [Path.map_comp, ← Category.assoc, postnikovCommonRightFixedCellClassWitness_projection,
    Category.assoc, postnikovCommonRightBasePath_zero]
  simp only [Category.assoc]

def postnikovCommonRightFixedZeroPathWitness : Path.Witness R
    (postnikovCommonRightZeroPathLeft R hn f c d) (postnikovCommonRightZeroPathRight R hn f c d) :=
  (postnikovCommonRightFixedCellClassWitness R hn f c d).postcomp
    (postnikovClassToZeroBase R (B.obj i).obj n hn 1)

lemma postnikovCommonRightFixedZeroPathWitness_projection :
    (postnikovCommonRightFixedZeroPathWitness R hn f c d).hom ≫
      Path.map R (SquareZero.projection _ _) =
    (postnikovCommonRightCellProjection R hn f c d ≫ postnikovCommonRightZeroBase R hn f c d) ≫
      Path.diagonal R (postnikov R (B.obj i).obj 0) := by
  change ((postnikovCommonRightFixedCellClassWitness R hn f c d).hom ≫
    Path.map R (postnikovClassToZeroBase R (B.obj i).obj n hn 1)) ≫ _ = _
  rw [Category.assoc, ← Path.map_comp, postnikovClassToZeroBase_projection]
  exact (postnikovCommonRightFixedCellClassWitness_zero R hn f c d).trans
    (congrArg (fun t => t ≫ Path.diagonal R (postnikov R (B.obj i).obj 0))
      (congrArg (fun t => postnikovCommonRightCellProjection R hn f c d ≫ t)
        (postnikovCommonRightZeroBase_num R hn f c d).symm))

def postnikovCommonRightFixedZeroRelativeWitness : Path.Witness R
    (postnikovCommonRightZeroPathSource R hn f c d) (postnikovCommonRightZeroPathTarget R hn f c d) :=
  SquareZero.baseChangeWitness _ _ _ _ _
    (postnikovCommonRightZeroPathLeft_projection R hn f c d)
    (postnikovCommonRightZeroPathRight_projection R hn f c d)
    (postnikovCommonRightFixedZeroPathWitness R hn f c d)
    (postnikovCommonRightFixedZeroPathWitness_projection R hn f c d)

lemma postnikovCommonRightFixedZeroRelativeWitness_projection :
    (postnikovCommonRightFixedZeroRelativeWitness R hn f c d).hom ≫
      Path.map R (SquareZero.projection _ _) =
    postnikovCommonRightCellProjection R hn f c d ≫
      Path.diagonal R (postnikovCommonClassBase R hn f c d) :=
  SquareZero.baseChangeWitness_relative _ _ _ _ _ _ _ _ _

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
