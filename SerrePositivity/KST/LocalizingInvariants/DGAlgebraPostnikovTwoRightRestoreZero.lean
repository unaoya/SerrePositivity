module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoRightImageNullPath

/-!
概要：元の右像と完成した分母の native 係数復元を、同じ零 class 標的へ照合する。
方針：元の係数同型の可逆性と全底変更三角形を使い、復元後の全経路像を固定する。
規約：係数のホモロジー像だけで比較しない。使われ方：W の模型経路の終点照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} {f : LevelHom A B}
  {j : ℕ} (d : PostnikovTwoClassInverseData R f j)

lemma rightImageCoefficientIso_zero_map :
    (SquareZero.coefficientIso (d.classBase R) (d.rightImageCoefficientIso R)).hom ≫
      SquareZero.baseChangeMap
        (postnikovCommonRightClassifyingBase R f d.baseInverse d.layerInverse d.target_le)
        (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1) =
    SquareZero.baseChangeMap
      (postnikovCommonClassRightImageBase R f d.baseInverse d.layerInverse d.target_le)
      (postnikovShiftedLayerBimodule R (B.obj j).obj 1 (by omega) 1) ≫
        postnikovClassToZeroBase R (B.obj j).obj 1 (by omega) 1 := by
  have hi : (SquareZero.coefficientIso (d.classBase R) (d.rightImageCoefficientIso R)).hom =
      (postnikovClassZeroRebaseIso R (B.obj j).obj (d.classBase R) 1 (by omega) 1
        (postnikovCommonClassRightImageBase R f d.baseInverse d.layerInverse d.target_le)
        (postnikovCommonRightClassifyingBase R f d.baseInverse d.layerInverse d.target_le)
        (postnikovCommonClassRightImageBase_zero R f d.baseInverse d.layerInverse d.target_le)).hom := by
    simp only [rightImageCoefficientIso, postnikovClassZeroRebaseIso,
      postnikovClassBaseZeroIso, SquareZero.restrictionEqualityIso, Iso.trans_hom,
      SquareZero.coefficientIso_hom, ← SquareZero.coefficientMap_comp]
  rw [hi]
  exact postnikovClassZeroRebaseIso_map R (B.obj j).obj (d.classBase R) 1 (by omega) 1 _ _ _

lemma rightImageClassRestore_zero : d.rightImageClassRestore R ≫
    postnikovClassToZeroBase R (B.obj j).obj 1 (by omega) 1 =
    SquareZero.baseChangeMap
      (postnikovCommonRightClassifyingBase R f d.baseInverse d.layerInverse d.target_le)
      (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1) := by
  apply (cancel_epi (SquareZero.coefficientIso (d.classBase R)
    (d.rightImageCoefficientIso R)).hom).1
  rw [← Category.assoc, rightImageClassRestore, SquareZero.coefficientRestore_triangle]
  exact (d.rightImageCoefficientIso_zero_map R).symm

lemma rightDenominatorClassRestore_zero : d.rightDenominatorClassRestore R ≫
    postnikovClassToZeroBase R (B.obj j).obj 1 (by omega) 1 =
    SquareZero.baseChangeMap
      (postnikovCommonRightClassifyingBase R f d.baseInverse d.layerInverse d.target_le)
      (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1) := by
  apply (cancel_epi (SquareZero.coefficientIso (d.classBase R)
    (d.rightDenominatorCoefficientIso R)).hom).1
  rw [← Category.assoc, d.rightDenominatorCoefficientIso_map R,
    d.rightDenominatorClassRestore_triangle R]
  exact (postnikovCommonRightDenDirectToZero_map R f d.baseInverse d.layerInverse
    d.target_le).symm

lemma fixedRightFollowingWitness_zero_map :
    (d.fixedRightFollowingWitness R).hom ≫ Path.map R
      (SquareZero.baseChangeMap
        (postnikovCommonRightClassifyingBase R f d.baseInverse d.layerInverse d.target_le)
        (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1)) =
    (d.fixedRightNativeFollowing R).hom :=
  SquareZero.baseChangeFollowingWitness_map _ _ _ _ _ _ _

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
