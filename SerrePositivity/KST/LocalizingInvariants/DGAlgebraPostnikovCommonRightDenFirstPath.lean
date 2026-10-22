module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightDenCompositeZero
public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightSourceOriginalPath
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
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (postnikovFunctor R 1)) i m hi)
  (d : PostnikovCommonLayerInverse R f c) {j : ℕ} (hj : j ≤ i)

def postnikovCommonRightSourceRefinedPath :=
  ((postnikovCommonRightTransitionLift R f c d hj
    (postnikovCommonRightFixedSourceRelative R f c d)).precomp
      (postnikovCommonRightToClassifying R f c d)).rebase
      (postnikovCommonRightToClassifying_projection R f c d)

def postnikovCommonRightDenFirstZeroPath :=
  (((postnikovCellImageForwardRelative R (B.obj d.zero.stage).obj (B.obj i).obj (B.obj j).obj
    (postnikovCommonClassBase R f c d) 1 (by omega)
    (postnikovOneRoofRefine R f c d.zero.source_le).roof.denominator
    (B.transition (d.zero.inverse_le.trans d.zero.stage_le)).hom
      (B.transition hj).hom).mapOver (𝟙 _)
    (postnikovCommonRightDenCompositeZeroIso R f c d hj).hom
    ((postnikovCommonRightDenCompositeZeroIso_projection R f c d hj).trans
      (Category.comp_id _).symm)).precomp
    (postnikovCommonRightImageToSecond R f c d)).rebase
    (q' := postnikovCommonClassStandardGlueProjection R f c d) (by
      rw [Category.comp_id]
      exact postnikovCommonRightImageToSecond_projection R f c d)

lemma postnikovCommonRightDenFirstZeroPath_map :
    (postnikovCommonRightDenFirstZeroPath R f c d hj).hom ≫ Path.map R
      (SquareZero.baseChangeMap (postnikovCommonRightClassifyingBase R f c d hj)
        (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1)) =
    postnikovCommonRightImageToSecond R f c d ≫
      (postnikovCellImageForwardRelative R (B.obj d.zero.stage).obj (B.obj i).obj (B.obj j).obj
        (postnikovCommonClassBase R f c d) 1 (by omega)
        (postnikovOneRoofRefine R f c d.zero.source_le).roof.denominator
        (B.transition (d.zero.inverse_le.trans d.zero.stage_le)).hom
      (B.transition hj).hom).hom ≫ Path.map R
      (SquareZero.baseChangeMap
        (((postnikovOneRoofRefine R f c d.zero.source_le).roof.denominator ≫
          postnikovMap R (B.transition (d.zero.inverse_le.trans d.zero.stage_le)).hom 1) ≫
          postnikovMap R (B.transition hj).hom 1)
        (postnikovShiftedLayerBimodule R (B.obj j).obj 1 (by omega) 1) ≫
          postnikovClassToZeroBase R (B.obj j).obj 1 (by omega) 1) := by
  change (postnikovCommonRightImageToSecond R f c d ≫
    ((postnikovCellImageForwardRelative R (B.obj d.zero.stage).obj (B.obj i).obj (B.obj j).obj
      (postnikovCommonClassBase R f c d) 1 (by omega)
      (postnikovOneRoofRefine R f c d.zero.source_le).roof.denominator
      (B.transition (d.zero.inverse_le.trans d.zero.stage_le)).hom (B.transition hj).hom).hom ≫
        Path.map R (postnikovCommonRightDenCompositeZeroIso R f c d hj).hom)) ≫ _ = _
  simp only [Category.assoc, ← Path.map_comp, postnikovCommonRightDenCompositeZeroIso_map]
  rfl

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
