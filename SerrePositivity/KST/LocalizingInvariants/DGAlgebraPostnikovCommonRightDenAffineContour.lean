module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightDenAffineImage
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeFollowingTransfer
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightGlueNaturality

/-!
概要：二段分母 affine 経路を、元の分母輪郭の全経路そのものへ同定する。
方針：同じ二 ImageWitness の底付き移送・前合成の合成保存を使う。
規約：元の第一辺・第二辺・輪郭の全射を保持。使われ方：直接遷移の比較との接続。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (postnikovFunctor R 1)) i m hi)
  (d : PostnikovCommonLayerInverse R f c) {j : ℕ} (hj : j ≤ i)

lemma postnikovCommonRightDenAffinePath_pair_hom :
    (postnikovCommonRightDenAffinePath R f c d hj).hom =
      (postnikovCommonRightDenZeroComposite R f c d hj).hom := by
  let v := postnikovCellImageForwardRelative R (B.obj d.zero.stage).obj (B.obj i).obj
    (B.obj j).obj (postnikovCommonClassBase R f c d) 1 (by omega)
    (postnikovOneRoofRefine R f c d.zero.source_le).roof.denominator
    (B.transition (d.zero.inverse_le.trans d.zero.stage_le)).hom (B.transition hj).hom
  let w := postnikovCellImageRelative R (B.obj i).obj (B.obj j).obj
    (postnikovCommonClassBase R f c d) 1 (by omega)
    ((postnikovOneRoofRefine R f c d.zero.source_le).roof.denominator ≫
      postnikovMap R (B.transition (d.zero.inverse_le.trans d.zero.stage_le)).hom 1)
    (B.transition hj).hom
  let k := (postnikovCommonRightDenCompositeZeroIso R f c d hj).hom
  let hk := (postnikovCommonRightDenCompositeZeroIso_projection R f c d hj).trans
    (Category.comp_id _).symm
  let a := postnikovCommonRightImageToSecond R f c d
  let hm := congrArg (fun t => a ≫ t)
    (SquareZero.RelativeWitness.mapOver_comp_hom (𝟙 _) k hk v w)
  let hp := SquareZero.RelativeWitness.precomp_comp_hom
    (v.mapOver (𝟙 _) k hk) (w.mapOver (𝟙 _) k hk) a
  exact (postnikovCommonRightDenAffinePath_image_hom R f c d hj).trans
    (hm.trans (hp.trans (SquareZero.RelativeWitness.comp_congr_hom_of_paths rfl rfl)))

lemma postnikovCommonRightDenAffinePath_contour_hom :
    (postnikovCommonRightDenAffinePath R f c d hj).hom =
      (postnikovCommonRightDenContourPath R f c d hj).hom := by
  let h := SquareZero.RelativeWitness.replaceHom_hom
    (postnikovCommonRightContourSourceRightRefined R f c d hj)
    (postnikovCommonRightDenZeroComposite R f c d hj).hom
    (postnikovCommonRightContourSourceRight_hom R f c d hj)
  exact (postnikovCommonRightDenAffinePath_pair_hom R f c d hj).trans h.symm

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
