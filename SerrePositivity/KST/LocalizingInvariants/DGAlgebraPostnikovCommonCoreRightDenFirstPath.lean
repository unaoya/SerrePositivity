module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightDenCompositeZero
public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightSourceOriginalPath
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCellImageForwardZero

/-!
概要：元の Γ 源上で、T の B 遷移後の持ち上げと零底 affine 分母側第一辺を取り出す。
方針：元の指定細分・実係数射を使い、同じ Γ 射影上の相対経路を保つ。
規約：全経路を変更しない。使われ方：二射影の一意性による分母側第一辺の実同定。
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
  (d : PostnikovCommonLayerInverse R hn f c) {j : ℕ} (hj : j ≤ i)

attribute [local instance] PostnikovRoofZeroSpan.refined_source_nonpositive
  PostnikovRoofZeroSpan.refined_target_nonpositive

def postnikovCommonRightSourceRefinedPath :=
  ((postnikovCommonRightTransitionLift R hn f c d hj
    (postnikovCommonRightFixedSourceRelative R hn f c d)).precomp
      (postnikovCommonRightToClassifying R hn f c d)).rebase
      (postnikovCommonRightToClassifying_projection R hn f c d)

def postnikovCommonRightDenFirstZeroPath :=
  (((postnikovCellImageForwardRelative R (B.obj d.zero.stage).obj (B.obj i).obj (B.obj j).obj
    (postnikovCommonClassBase R hn f c d) n hn
    (roofRefine R hn f c d.zero.source_le).roof.denominator
    (B.transition (d.zero.inverse_le.trans d.zero.stage_le)).hom
      (B.transition hj).hom).mapOver (𝟙 _)
    (postnikovCommonRightDenCompositeZeroIso R hn f c d hj).hom
    ((postnikovCommonRightDenCompositeZeroIso_projection R hn f c d hj).trans
      (Category.comp_id _).symm)).precomp
    (postnikovCommonRightImageToSecond R hn f c d)).rebase
    (q' := postnikovCommonClassStandardGlueProjection R hn f c d) (by
      rw [Category.comp_id]
      exact postnikovCommonRightImageToSecond_projection R hn f c d)

lemma postnikovCommonRightDenFirstZeroPath_map :
    (postnikovCommonRightDenFirstZeroPath R hn f c d hj).hom ≫ Path.map R
      (SquareZero.baseChangeMap (postnikovCommonRightClassifyingBase R hn f c d hj)
        (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj n) 1)) =
    postnikovCommonRightImageToSecond R hn f c d ≫
      (postnikovCellImageForwardRelative R (B.obj d.zero.stage).obj (B.obj i).obj (B.obj j).obj
        (postnikovCommonClassBase R hn f c d) n hn
        (roofRefine R hn f c d.zero.source_le).roof.denominator
        (B.transition (d.zero.inverse_le.trans d.zero.stage_le)).hom
      (B.transition hj).hom).hom ≫ Path.map R
      (SquareZero.baseChangeMap
        (((roofRefine R hn f c d.zero.source_le).roof.denominator ≫
          postnikovMap R (B.transition (d.zero.inverse_le.trans d.zero.stage_le)).hom n) ≫
          postnikovMap R (B.transition hj).hom n)
        (postnikovShiftedLayerBimodule R (B.obj j).obj n hn 1) ≫
          postnikovClassToZeroBase R (B.obj j).obj n hn 1) := by
  change (postnikovCommonRightImageToSecond R hn f c d ≫
    ((postnikovCellImageForwardRelative R (B.obj d.zero.stage).obj (B.obj i).obj (B.obj j).obj
      (postnikovCommonClassBase R hn f c d) n hn
      (roofRefine R hn f c d.zero.source_le).roof.denominator
      (B.transition (d.zero.inverse_le.trans d.zero.stage_le)).hom (B.transition hj).hom).hom ≫
        Path.map R (postnikovCommonRightDenCompositeZeroIso R hn f c d hj).hom)) ≫ _ = _
  simp only [Category.assoc, ← Path.map_comp, postnikovCommonRightDenCompositeZeroIso_map]
  rfl

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
