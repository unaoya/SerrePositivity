module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightZeroNormalize
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraCellPathOperations

/-!
概要：元の三つの class 比較経路を共通零標的で貼り合わせ、元の共通底へ相対化する。
方針：二度の cell 経路合成と向き反転を使い、非正次数共通源と定数零射影を回収する。
規約：源の元の共通底への各次数全射準同型を保持。使われ方：class 像の整合の実経路。
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

local instance zeroGlue_target_lowerBound : (postnikov R (B.obj i).obj 0).X.IsStrictlyGE 0 := by
  simpa only [neg_zero] using postnikov_lowerBound R (B.obj i).obj 0

abbrev postnikovCommonRightZeroGlueSource :=
  cellPathNonpositiveSource R (postnikovCommonRightCellSource R f c d)

def postnikovCommonRightZeroGlueProjection : postnikovCommonRightZeroGlueSource R f c d ⟶
    postnikovCommonClassBase R f c d :=
  cellPathNonpositiveProjection R (postnikovCommonRightCellSource R f c d) ≫
    postnikovCommonRightCellProjection R f c d

lemma postnikovCommonRightZeroGlueProjection_quasiIso :
    QuasiIso (postnikovCommonRightZeroGlueProjection R f c d).hom :=
  quasiIso_comp _ _
    (hφ := cellPathNonpositiveProjection_quasiIso R _ (by
      change (postnikovCommonRightCellSource R f c d).X.IsLE 0
      infer_instance))
    (hφ' := postnikovCommonRightCellProjection_quasiIso R f c d)

lemma postnikovCommonRightZeroGlueProjection_surjective (n : ℤ) :
    Function.Surjective ((postnikovCommonRightZeroGlueProjection R f c d).hom.f n) :=
  (postnikovCommonRightCellProjection_surjective R f c d n).comp
    (cellPathNonpositiveProjection_surjective R (postnikovCommonRightCellSource R f c d) n)

def postnikovCommonRightZeroGlueWitness : Path.Witness R
    (cellPathNonpositiveProjection R (postnikovCommonRightCellSource R f c d) ≫
      postnikovCommonRightZeroImageTarget R f c d)
    (cellPathNonpositiveProjection R (postnikovCommonRightCellSource R f c d) ≫
      postnikovCommonRightZeroImageSource R f c d) :=
  (((postnikovCommonRightZeroImageTargetWitness R f c d).cellComp R
    (postnikovCommonRightZeroStandardWitness R f c d)).cellComp R
      ((postnikovCommonRightZeroImageSourceWitness R f c d).cellReverse
        R)).precompNonpositiveDouble R

lemma postnikovCommonRightZeroGlueLeft_projection :
    (cellPathNonpositiveProjection R (postnikovCommonRightCellSource R f c d) ≫
      postnikovCommonRightZeroImageTarget R f c d) ≫ SquareZero.projection _ _ =
    postnikovCommonRightZeroGlueProjection R f c d ≫ postnikovCommonRightZeroBase R f c d := by
  rw [Category.assoc, postnikovCommonRightZeroImageTarget_projection, ← Category.assoc]
  rfl

lemma postnikovCommonRightZeroGlueRight_projection :
    (cellPathNonpositiveProjection R (postnikovCommonRightCellSource R f c d) ≫
      postnikovCommonRightZeroImageSource R f c d) ≫ SquareZero.projection _ _ =
    postnikovCommonRightZeroGlueProjection R f c d ≫ postnikovCommonRightZeroBase R f c d := by
  rw [Category.assoc, postnikovCommonRightZeroImageSource_projection, ← Category.assoc]
  rfl

lemma postnikovCommonRightZeroGlueWitness_projection :
    (postnikovCommonRightZeroGlueWitness R f c d).hom ≫ Path.map R (SquareZero.projection _ _) =
    (postnikovCommonRightZeroGlueProjection R f c d ≫ postnikovCommonRightZeroBase R f c d) ≫
      Path.diagonal R (postnikov R (B.obj i).obj 0) :=
  (Path.Witness.hom_eq_constant R
    ((postnikovCommonRightZeroGlueWitness R f c d).postcomp (SquareZero.projection _ _))).trans
      (congrArg (fun (t : postnikovCommonRightZeroGlueSource R f c d ⟶
        postnikov R (B.obj i).obj 0) => t ≫ Path.diagonal R (postnikov R (B.obj i).obj 0))
        (postnikovCommonRightZeroGlueLeft_projection R f c d))

def postnikovCommonRightZeroGlueLeft := SquareZero.baseChangeLift
  (postnikovCommonRightZeroBase R f c d)
  (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj i).obj 1) 1)
  (postnikovCommonRightZeroGlueProjection R f c d)
  (cellPathNonpositiveProjection R (postnikovCommonRightCellSource R f c d) ≫
    postnikovCommonRightZeroImageTarget R f c d)
    (postnikovCommonRightZeroGlueLeft_projection R f c d)

def postnikovCommonRightZeroGlueRight := SquareZero.baseChangeLift
  (postnikovCommonRightZeroBase R f c d)
  (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj i).obj 1) 1)
  (postnikovCommonRightZeroGlueProjection R f c d)
  (cellPathNonpositiveProjection R (postnikovCommonRightCellSource R f c d) ≫
    postnikovCommonRightZeroImageSource R f c d)
    (postnikovCommonRightZeroGlueRight_projection R f c d)

def postnikovCommonRightZeroGlueRelativeWitness : Path.Witness R
    (postnikovCommonRightZeroGlueLeft R f c d)
    (postnikovCommonRightZeroGlueRight R f c d) :=
  SquareZero.baseChangeWitness _ _ _ _ _ _ _ (postnikovCommonRightZeroGlueWitness R f c d)
    (postnikovCommonRightZeroGlueWitness_projection R f c d)

lemma postnikovCommonRightZeroGlueRelativeWitness_projection :
    (postnikovCommonRightZeroGlueRelativeWitness R f c d).hom ≫
      Path.map R (SquareZero.projection _ _) =
    postnikovCommonRightZeroGlueProjection R f c d ≫
      Path.diagonal R (postnikovCommonClassBase R f c d) :=
  SquareZero.baseChangeWitness_relative _ _ _ _ _ _ _ _ _

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
