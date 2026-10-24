module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightClassifyingContour
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroBaseChangeDoublePath

/-!
概要：元の classifying 二重経路を、指定した同じ共通底 P 上へ持ち上げる。
方針：零底射の実因子化と二重経路 pullback の持ち上げを使う。
規約：底と class の全二重経路を保持。使われ方：元の Γ 模型での輪郭比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
open ProExcision
variable (R : Type u) [CommRing R] {n : ℤ} (hn : 0 ≤ n)
  {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (lowerFunctor R n hn)) i m hi)
  (d : PostnikovCommonLayerInverse R hn f c) {j : ℕ} (hj : j ≤ i)

attribute [local instance] PostnikovRoofZeroSpan.refined_source_nonpositive
  PostnikovRoofZeroSpan.refined_target_nonpositive

def postnikovCommonRightClassifyingBase :
    postnikovCommonClassBase R hn f c d ⟶ postnikov R (B.obj j).obj 0 :=
  postnikovCommonRightBase R hn f c d ≫ postnikovMap R (B.transition hj).hom n ≫
    postnikovTransition R (B.obj j).obj n 0 (by omega)

def postnikovCommonRightClassifyingProjection :
    cellResolution R (postnikovCommonRightCellSource R hn f c d) ⟶ postnikovCommonClassBase R hn f c d :=
  cellAugmentation R (postnikovCommonRightCellSource R hn f c d) ≫
    postnikovCommonRightCellProjection R hn f c d

lemma postnikovCommonRightClassifyingProjection_quasiIso :
    QuasiIso (postnikovCommonRightClassifyingProjection R hn f c d).hom := by
  have := cellAugmentation_quasiIso R (postnikovCommonRightCellSource R hn f c d)
  have := postnikovCommonRightCellProjection_quasiIso R hn f c d
  exact quasiIso_comp _ _

lemma postnikovCommonRightClassifyingProjection_surjective (degree : ℤ) :
    Function.Surjective ((postnikovCommonRightClassifyingProjection R hn f c d).hom.f degree) := by
  exact (postnikovCommonRightCellProjection_surjective R hn f c d degree).comp
    (cellAugmentation_surjective R (postnikovCommonRightCellSource R hn f c d) degree)

lemma postnikovCommonRightClassifyingProjection_factor :
    postnikovCommonRightClassifyingProjection R hn f c d ≫
      postnikovCommonRightClassifyingBase R hn f c d hj =
        postnikovCommonRightClassifyingZeroProjection R hn f c d hj := by
  simp only [postnikovCommonRightClassifyingProjection, postnikovCommonRightClassifyingBase,
    postnikovCommonRightClassifyingZeroProjection, Category.assoc]

lemma postnikovCommonRightClassifyingBaseChange_condition :
    ((postnikovCommonRightClassifyingProjection R hn f c d ≫
      Path.diagonal R (postnikovCommonClassBase R hn f c d)) ≫
        Path.diagonal R (Path.algebra R (postnikovCommonClassBase R hn f c d))) ≫
          Path.map R (Path.map R (postnikovCommonRightClassifyingBase R hn f c d hj)) =
    (postnikovCommonRightClassifyingZeroSquare R hn f c d hj).hom ≫
      Path.map R (Path.map R (SquareZero.projection _ _)) := by
  rw [postnikovCommonRightClassifyingZeroSquare_projection]
  simp only [Category.assoc, Path.diagonal_naturality]
  rw [reassoc_of% (Path.diagonal_naturality R (postnikovCommonRightClassifyingBase R hn f c d hj)),
    ← Category.assoc (postnikovCommonRightClassifyingProjection R hn f c d)
      (postnikovCommonRightClassifyingBase R hn f c d hj),
    postnikovCommonRightClassifyingProjection_factor]

def postnikovCommonRightClassifyingBaseChangeHom :
    cellResolution R (postnikovCommonRightCellSource R hn f c d) ⟶ Path.algebra R
      (Path.algebra R (SquareZero.algebra (postnikovCommonClassBase R hn f c d)
        (bimoduleRestrict (postnikovCommonRightClassifyingBase R hn f c d hj)
          (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj n) 1)))) :=
  SquareZero.baseChangeDoublePathLift (postnikovCommonRightClassifyingBase R hn f c d hj) _
    ((postnikovCommonRightClassifyingProjection R hn f c d ≫ Path.diagonal R _) ≫ Path.diagonal R _)
    (postnikovCommonRightClassifyingZeroSquare R hn f c d hj).hom
    (postnikovCommonRightClassifyingBaseChange_condition R hn f c d hj)

lemma postnikovCommonRightClassifyingBaseChangeHom_projection :
    postnikovCommonRightClassifyingBaseChangeHom R hn f c d hj ≫
      Path.map R (Path.map R (SquareZero.projection _ _)) =
    (postnikovCommonRightClassifyingProjection R hn f c d ≫
      Path.diagonal R (postnikovCommonClassBase R hn f c d)) ≫
        Path.diagonal R (Path.algebra R (postnikovCommonClassBase R hn f c d)) :=
  SquareZero.baseChangeDoublePathLift_projection _ _ _ _ _

lemma postnikovCommonRightClassifyingBaseChangeHom_map :
    postnikovCommonRightClassifyingBaseChangeHom R hn f c d hj ≫
      Path.map R (Path.map R (SquareZero.baseChangeMap
        (postnikovCommonRightClassifyingBase R hn f c d hj)
        (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj n) 1))) =
    (postnikovCommonRightClassifyingZeroSquare R hn f c d hj).hom :=
  SquareZero.baseChangeDoublePathLift_map _ _ _ _ _

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
