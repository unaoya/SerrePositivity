module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightAffineFixedGlue
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightClassGlue

/-!
概要：指定右経路の affine 貼合せを、元の共通源と native class 標的へ戻す。
方針：既存の源射影で前合成し、同じ底変更同型の逆を使う。
規約：元の二つの右 class 像と同じ両端を保持。使われ方：整合する Γ class 互換性。
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

def postnikovCommonRightFixedZeroGlueWitness : Path.Witness R
    (cellPathNonpositiveProjection R (postnikovCommonRightCellSource R hn f c d) ≫
      postnikovCommonRightZeroImageTarget R hn f c d)
    (cellPathNonpositiveProjection R (postnikovCommonRightCellSource R hn f c d) ≫
      postnikovCommonRightZeroImageSource R hn f c d) :=
  ((postnikovCommonRightAffineFixedGlue R hn f c d).precomp
    (cellPathNonpositiveProjection R (postnikovCommonRightCellSource R hn f c d))).toWitness

lemma postnikovCommonRightFixedZeroGlueWitness_projection :
    (postnikovCommonRightFixedZeroGlueWitness R hn f c d).hom ≫
      Path.map R (SquareZero.projection _ _) =
    (postnikovCommonRightZeroGlueProjection R hn f c d ≫ postnikovCommonRightZeroBase R hn f c d) ≫
      Path.diagonal R (postnikov R (B.obj i).obj 0) := by
  change (cellPathNonpositiveProjection R (postnikovCommonRightCellSource R hn f c d) ≫
    (postnikovCommonRightAffineFixedGlue R hn f c d).hom) ≫ _ = _
  rw [Category.assoc, (postnikovCommonRightAffineFixedGlue R hn f c d).projection_eq]
  simp only [postnikovCommonRightZeroGlueProjection, Category.assoc]

def postnikovCommonRightFixedZeroGlueRelativeWitness : Path.Witness R
    (postnikovCommonRightZeroGlueLeft R hn f c d) (postnikovCommonRightZeroGlueRight R hn f c d) :=
  SquareZero.baseChangeWitness _ _ _ _ _ _ _ (postnikovCommonRightFixedZeroGlueWitness R hn f c d)
    (postnikovCommonRightFixedZeroGlueWitness_projection R hn f c d)

lemma postnikovCommonRightFixedZeroGlueRelativeWitness_projection :
    (postnikovCommonRightFixedZeroGlueRelativeWitness R hn f c d).hom ≫
      Path.map R (SquareZero.projection _ _) =
    postnikovCommonRightZeroGlueProjection R hn f c d ≫
      Path.diagonal R (postnikovCommonClassBase R hn f c d) :=
  SquareZero.baseChangeWitness_relative _ _ _ _ _ _ _ _ _

def postnikovCommonRightFixedClassGlueWitness : Path.Witness R
    (postnikovCommonRightGlueTarget R hn f c d) (postnikovCommonRightGlueSource R hn f c d) where
  hom := (postnikovCommonRightFixedZeroGlueRelativeWitness R hn f c d).hom ≫
    Path.map R (postnikovCommonRightZeroBaseIso R hn f c d).inv
  source_eq := by
    rw [Category.assoc, Path.map_source, ← Category.assoc,
      (postnikovCommonRightFixedZeroGlueRelativeWitness R hn f c d).source_eq,
      postnikovCommonRightZeroGlueLeft_eq, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  target_eq := by
    rw [Category.assoc, Path.map_target, ← Category.assoc,
      (postnikovCommonRightFixedZeroGlueRelativeWitness R hn f c d).target_eq,
      postnikovCommonRightZeroGlueRight_eq, Category.assoc, Iso.hom_inv_id, Category.comp_id]

lemma postnikovCommonRightFixedClassGlueWitness_projection :
    (postnikovCommonRightFixedClassGlueWitness R hn f c d).hom ≫
      Path.map R (SquareZero.projection _ _) = postnikovCommonRightZeroGlueProjection R hn f c d ≫
        Path.diagonal R (postnikovCommonClassBase R hn f c d) := by
  change (_ ≫ Path.map R (postnikovCommonRightZeroBaseIso R hn f c d).inv) ≫ _ = _
  rw [Category.assoc, ← Path.map_comp, postnikovCommonRightZeroBaseIso_inv_projection,
    postnikovCommonRightFixedZeroGlueRelativeWitness_projection]

def postnikovCommonRightFixedClassGlueRelative : SquareZero.RelativeWitness
    (postnikovCommonRightZeroGlueProjection R hn f c d)
    (DGBimoduleShift.obj (postnikovCommonRightLayer R hn f c d) 1)
    (postnikovCommonRightGlueTarget R hn f c d) (postnikovCommonRightGlueSource R hn f c d) where
  toWitness := postnikovCommonRightFixedClassGlueWitness R hn f c d
  projection_eq := postnikovCommonRightFixedClassGlueWitness_projection R hn f c d

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
