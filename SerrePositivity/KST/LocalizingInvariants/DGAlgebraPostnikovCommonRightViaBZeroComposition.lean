module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightContourLeftComparison
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativePathCompositionCongr

/-!
概要：Γ 源上の零底 affineViaB 経路を、元の第一辺・第二辺の affine 合成へ同定する。
方針：元の ImageWitness 合成の表示と、後合成・前合成の厳密な保存を使う。
規約：全経路を保持。使われ方：T′L の同定から元の二因子分解比較へ接続する。
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

def postnikovCommonRightViaBZeroComposite :=
  (postnikovCommonRightViaBFirstZeroPath R f c d hj).comp
    (postnikovCommonRightViaBSecondZeroPath R f c d hj)

lemma postnikovCommonRightZeroAffineViaB_pair_hom :
    (postnikovCommonRightZeroAffineViaB R f c d hj).hom =
      (postnikovCommonRightViaBZeroComposite R f c d hj).hom := by
  let v := postnikovCellImageForwardRelative R (A.obj i).obj (B.obj i).obj (B.obj j).obj
    (postnikovCommonClassBase R f c d) 1 (by omega)
    (postnikovOneRoofRefine R f c d.zero.source_le).roof.numerator
    (f.app i).hom (B.transition hj).hom
  let w := postnikovCellImageRelative R (B.obj i).obj (B.obj j).obj
    (postnikovCommonClassBase R f c d) 1 (by omega)
    ((postnikovOneRoofRefine R f c d.zero.source_le).roof.numerator ≫
      postnikovMap R (f.app i).hom 1) (B.transition hj).hom
  let k := postnikovCommonRightViaBImageToZero R f c d hj
  let hk := (postnikovCommonRightViaBImageToZero_projection R f c d hj).trans
    (Category.comp_id _).symm
  let e := postnikovCommonRightImageToSecond R f c d
  have hm := congrArg (fun t => e ≫ t)
    (SquareZero.RelativeWitness.mapOver_comp_hom (𝟙 _) k hk v w)
  have hp := SquareZero.RelativeWitness.precomp_comp_hom
    (v.mapOver (𝟙 _) k hk) (w.mapOver (𝟙 _) k hk) e
  rw [postnikovCommonRightZeroAffineViaB_image_hom R f c d hj]
  exact hm.trans (hp.trans
    (SquareZero.RelativeWitness.comp_congr_hom_of_paths rfl rfl))

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
