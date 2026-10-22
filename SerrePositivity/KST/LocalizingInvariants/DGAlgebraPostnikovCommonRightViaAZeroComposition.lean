module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightViaASecondZero
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightViaAFirstZero
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativePathCompositionCongr

/-!
概要：Γ 源上の零底 affineViaA 経路を、元の第一辺・第二辺の affine 合成へ同定する。
方針：元の ImageWitness 合成の表示と、後合成・前合成の厳密な保存を使う。
規約：全経路を保持。使われ方：native 標準経路像の同定から元の二因子分解比較へ接続する。
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

def postnikovCommonRightViaAZeroComposite :=
  (postnikovCommonRightViaAFirstZeroPath R f c d hj).comp
    (postnikovCommonRightViaASecondZeroPath R f c d hj)

lemma postnikovCommonRightZeroAffineViaA_pair_hom :
    (postnikovCommonRightZeroAffineViaA R f c d hj).hom =
      (postnikovCommonRightViaAZeroComposite R f c d hj).hom := by
  let v := postnikovCellImageForwardRelative R (A.obj i).obj (A.obj j).obj (B.obj j).obj
    (postnikovCommonClassBase R f c d) 1 (by omega)
    (postnikovOneRoofRefine R f c d.zero.source_le).roof.numerator
    (A.transition hj).hom (f.app j).hom
  let w := postnikovCellImageRelative R (A.obj j).obj (B.obj j).obj
    (postnikovCommonClassBase R f c d) 1 (by omega)
    ((postnikovOneRoofRefine R f c d.zero.source_le).roof.numerator ≫
      postnikovMap R (A.transition hj).hom 1) (f.app j).hom
  let k := postnikovCommonRightViaAImageToZero R f c d hj
  let hk := (postnikovCommonRightViaAImageToZero_projection R f c d hj).trans
    (Category.comp_id _).symm
  let e := postnikovCommonRightImageToSecond R f c d
  have hm := congrArg (fun t => e ≫ t)
    (SquareZero.RelativeWitness.mapOver_comp_hom (𝟙 _) k hk v w)
  have hp := SquareZero.RelativeWitness.precomp_comp_hom
    (v.mapOver (𝟙 _) k hk) (w.mapOver (𝟙 _) k hk) e
  rw [postnikovCommonRightZeroAffineViaA_image_hom R f c d hj]
  exact hm.trans (hp.trans
    (SquareZero.RelativeWitness.comp_congr_hom_of_paths rfl rfl))

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
