module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightZeroNormalize
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
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
open ProExcision
variable (R : Type u) [CommRing R] {n : ℤ} (hn : 0 ≤ n)
  {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (lowerFunctor R n hn)) i m hi)
  (d : PostnikovCommonLayerInverse R hn f c)

attribute [local instance] PostnikovRoofZeroSpan.refined_source_nonpositive
  PostnikovRoofZeroSpan.refined_target_nonpositive

local instance zeroGlue_target_lowerBound : (postnikov R (B.obj i).obj 0).X.IsStrictlyGE 0 := by
  simpa only [neg_zero] using postnikov_lowerBound R (B.obj i).obj 0

abbrev postnikovCommonRightZeroGlueSource :=
  cellPathNonpositiveSource R (postnikovCommonRightCellSource R hn f c d)

def postnikovCommonRightZeroGlueProjection : postnikovCommonRightZeroGlueSource R hn f c d ⟶
    postnikovCommonClassBase R hn f c d :=
  cellPathNonpositiveProjection R (postnikovCommonRightCellSource R hn f c d) ≫
    postnikovCommonRightCellProjection R hn f c d

lemma postnikovCommonRightZeroGlueProjection_quasiIso :
    QuasiIso (postnikovCommonRightZeroGlueProjection R hn f c d).hom :=
  quasiIso_comp _ _
    (hφ := cellPathNonpositiveProjection_quasiIso R _ (by
      change (postnikovCommonRightCellSource R hn f c d).X.IsLE 0
      infer_instance))
    (hφ' := postnikovCommonRightCellProjection_quasiIso R hn f c d)

lemma postnikovCommonRightZeroGlueProjection_surjective (degree : ℤ) :
    Function.Surjective ((postnikovCommonRightZeroGlueProjection R hn f c d).hom.f degree) :=
  (postnikovCommonRightCellProjection_surjective R hn f c d degree).comp
    (cellPathNonpositiveProjection_surjective R (postnikovCommonRightCellSource R hn f c d) degree)

def postnikovCommonRightZeroGlueWitness : Path.Witness R
    (cellPathNonpositiveProjection R (postnikovCommonRightCellSource R hn f c d) ≫
      postnikovCommonRightZeroImageTarget R hn f c d)
    (cellPathNonpositiveProjection R (postnikovCommonRightCellSource R hn f c d) ≫
      postnikovCommonRightZeroImageSource R hn f c d) :=
  (((postnikovCommonRightZeroImageTargetWitness R hn f c d).cellComp R
    (postnikovCommonRightZeroStandardWitness R hn f c d)).cellComp R
      ((postnikovCommonRightZeroImageSourceWitness R hn f c d).cellReverse
        R)).precompNonpositiveDouble R

lemma postnikovCommonRightZeroGlueLeft_projection :
    (cellPathNonpositiveProjection R (postnikovCommonRightCellSource R hn f c d) ≫
      postnikovCommonRightZeroImageTarget R hn f c d) ≫ SquareZero.projection _ _ =
    postnikovCommonRightZeroGlueProjection R hn f c d ≫ postnikovCommonRightZeroBase R hn f c d := by
  rw [Category.assoc, postnikovCommonRightZeroImageTarget_projection, ← Category.assoc]
  rfl

lemma postnikovCommonRightZeroGlueRight_projection :
    (cellPathNonpositiveProjection R (postnikovCommonRightCellSource R hn f c d) ≫
      postnikovCommonRightZeroImageSource R hn f c d) ≫ SquareZero.projection _ _ =
    postnikovCommonRightZeroGlueProjection R hn f c d ≫ postnikovCommonRightZeroBase R hn f c d := by
  rw [Category.assoc, postnikovCommonRightZeroImageSource_projection, ← Category.assoc]
  rfl

lemma postnikovCommonRightZeroGlueWitness_projection :
    (postnikovCommonRightZeroGlueWitness R hn f c d).hom ≫ Path.map R (SquareZero.projection _ _) =
    (postnikovCommonRightZeroGlueProjection R hn f c d ≫ postnikovCommonRightZeroBase R hn f c d) ≫
      Path.diagonal R (postnikov R (B.obj i).obj 0) :=
  (Path.Witness.hom_eq_constant R
    ((postnikovCommonRightZeroGlueWitness R hn f c d).postcomp (SquareZero.projection _ _))).trans
      (congrArg (fun (t : postnikovCommonRightZeroGlueSource R hn f c d ⟶
        postnikov R (B.obj i).obj 0) => t ≫ Path.diagonal R (postnikov R (B.obj i).obj 0))
        (postnikovCommonRightZeroGlueLeft_projection R hn f c d))

def postnikovCommonRightZeroGlueLeft := SquareZero.baseChangeLift
  (postnikovCommonRightZeroBase R hn f c d)
  (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj i).obj n) 1)
  (postnikovCommonRightZeroGlueProjection R hn f c d)
  (cellPathNonpositiveProjection R (postnikovCommonRightCellSource R hn f c d) ≫
    postnikovCommonRightZeroImageTarget R hn f c d)
    (postnikovCommonRightZeroGlueLeft_projection R hn f c d)

def postnikovCommonRightZeroGlueRight := SquareZero.baseChangeLift
  (postnikovCommonRightZeroBase R hn f c d)
  (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj i).obj n) 1)
  (postnikovCommonRightZeroGlueProjection R hn f c d)
  (cellPathNonpositiveProjection R (postnikovCommonRightCellSource R hn f c d) ≫
    postnikovCommonRightZeroImageSource R hn f c d)
    (postnikovCommonRightZeroGlueRight_projection R hn f c d)

def postnikovCommonRightZeroGlueRelativeWitness : Path.Witness R
    (postnikovCommonRightZeroGlueLeft R hn f c d)
    (postnikovCommonRightZeroGlueRight R hn f c d) :=
  SquareZero.baseChangeWitness _ _ _ _ _ _ _ (postnikovCommonRightZeroGlueWitness R hn f c d)
    (postnikovCommonRightZeroGlueWitness_projection R hn f c d)

lemma postnikovCommonRightZeroGlueRelativeWitness_projection :
    (postnikovCommonRightZeroGlueRelativeWitness R hn f c d).hom ≫
      Path.map R (SquareZero.projection _ _) =
    postnikovCommonRightZeroGlueProjection R hn f c d ≫
      Path.diagonal R (postnikovCommonClassBase R hn f c d) :=
  SquareZero.baseChangeWitness_relative _ _ _ _ _ _ _ _ _

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
