module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonClassStandardOriginalZero
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightViaAFirstZero

/-!
概要：native 標準経路の右像を、元の ViaA 第一辺の同じ零 class 像へ全射で同定する。
方針：指定した第一 ImageWitness の係数移送の零底公式を同じ Γ 射で前合成する。
規約：native 標準経路と ViaA の経路を選び直さない。使われ方：右 class 合成の接続。
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

lemma postnikovCommonClassFixedStandardMapped_first_hom :
    (postnikovCommonClassFixedStandardMappedRelative R f c d hj).hom =
    (postnikovCommonRightViaAFirstZeroPath R f c d hj).hom ≫ Path.map R
      (SquareZero.baseChangeMap (postnikovCommonRightClassifyingBase R f c d hj)
        (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1)) := by
  rw [postnikovCommonClassFixedStandardMapped_original_hom,
    postnikovCommonRightViaAFirstZeroPath_map]
  have h := postnikovCellImageForwardRelative_zero_map R (A.obj i).obj (A.obj j).obj
    (B.obj j).obj (postnikovCommonClassBase R f c d) 1 (by omega)
    (postnikovOneRoofRefine R f c d.zero.source_le).roof.numerator
    (A.transition hj).hom (f.app j).hom
  exact (congrArg (fun k => postnikovCommonRightImageToSecond R f c d ≫ k) h).symm

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
