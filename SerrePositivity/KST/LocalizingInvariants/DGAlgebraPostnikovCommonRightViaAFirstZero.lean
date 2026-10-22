module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightViaAImageMap
public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightTargetFirstPath
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCellImageForwardZero

/-!
概要：元の Γ 源上で、A 遷移と fⱼ の零底 affine 第一辺を取り出す。
方針：元の指定細分・ViaA の実係数射を使い、同じ Γ 射影上の相対経路を保つ。
規約：全経路を変更しない。使われ方：native 標準経路との全経路の同定。
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

def postnikovCommonRightViaAFirstZeroPath :=
  (((postnikovCellImageForwardRelative R (A.obj i).obj (A.obj j).obj (B.obj j).obj
    (postnikovCommonClassBase R f c d) 1 (by omega)
    (postnikovOneRoofRefine R f c d.zero.source_le).roof.numerator
    (A.transition hj).hom (f.app j).hom).mapOver (𝟙 _)
    (postnikovCommonRightViaAImageToZero R f c d hj)
    ((postnikovCommonRightViaAImageToZero_projection R f c d hj).trans
      (Category.comp_id _).symm)).precomp
    (postnikovCommonRightImageToSecond R f c d)).rebase
    (q' := postnikovCommonClassStandardGlueProjection R f c d) (by
      rw [Category.comp_id]
      exact postnikovCommonRightImageToSecond_projection R f c d)

lemma postnikovCommonRightViaAFirstZeroPath_map :
    (postnikovCommonRightViaAFirstZeroPath R f c d hj).hom ≫ Path.map R
      (SquareZero.baseChangeMap (postnikovCommonRightClassifyingBase R f c d hj)
        (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1)) =
    postnikovCommonRightImageToSecond R f c d ≫
      (postnikovCellImageForwardRelative R (A.obj i).obj (A.obj j).obj (B.obj j).obj
        (postnikovCommonClassBase R f c d) 1 (by omega)
        (postnikovOneRoofRefine R f c d.zero.source_le).roof.numerator
        (A.transition hj).hom (f.app j).hom).hom ≫ Path.map R
      (SquareZero.baseChangeMap
        (((postnikovOneRoofRefine R f c d.zero.source_le).roof.numerator ≫
          postnikovMap R (A.transition hj).hom 1) ≫ postnikovMap R (f.app j).hom 1)
        (postnikovShiftedLayerBimodule R (B.obj j).obj 1 (by omega) 1) ≫
          postnikovClassToZeroBase R (B.obj j).obj 1 (by omega) 1) := by
  change (postnikovCommonRightImageToSecond R f c d ≫
    ((postnikovCellImageForwardRelative R (A.obj i).obj (A.obj j).obj (B.obj j).obj
      (postnikovCommonClassBase R f c d) 1 (by omega)
      (postnikovOneRoofRefine R f c d.zero.source_le).roof.numerator
      (A.transition hj).hom (f.app j).hom).hom ≫
        Path.map R (postnikovCommonRightViaAImageToZero R f c d hj))) ≫ _ = _
  simp only [Category.assoc, ← Path.map_comp, postnikovCommonRightViaAImageToZero_map]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
