module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoFixedRightDirectCoefficientModel
public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonClassFixedRightRestored

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSuccessorFixedRightNativeFollowing

/-!
概要：fixed 模型射の後続に使う元の fⱼ 自然性と W を、同じ零底上で束ねる。
方針：全経路を保つ底表示の変更と、元の affine 合成の結合則を使う。
規約：元の native class 合成を変更しない。使われ方：実模型への後続経路の接合。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} {f : LevelHom A B}
  {j : ℕ} (d : PostnikovTwoClassInverseData R f j)

def fixedRightNativeCompatibility :=
  PostnikovSuccessorClassInverseData.fixedRightNativeCompatibility
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

def fixedRightNativeFollowing :=
  PostnikovSuccessorClassInverseData.fixedRightNativeFollowing
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma fixedRightNativeCompatibility_hom : (d.fixedRightNativeCompatibility R).hom =
    (postnikovCommonClassFixedCompatibilityMappedRelative R f d.baseInverse d.layerInverse
      d.target_le d.inverse).hom :=
  PostnikovSuccessorClassInverseData.fixedRightNativeCompatibility_hom
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma fixedRightNativeFollowing_comp_hom :
    ((d.fixedRightNativeCompatibility R).comp (d.fixedRightNativeFollowing R)).hom =
    (postnikovCommonClassFixedRightCompletedPath R f d.baseInverse d.layerInverse
      d.target_le d.inverse).hom :=
  PostnikovSuccessorClassInverseData.fixedRightNativeFollowing_comp_hom
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma fixedRightDirectCoefficientWitness_native_map :
    (d.fixedRightDirectCoefficientWitness R).hom ≫ Path.map R
      (SquareZero.baseChangeMap
        (postnikovCommonRightClassifyingBase R f d.baseInverse d.layerInverse d.target_le)
        (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1)) =
    (d.fixedRightNativeCompatibility R).hom :=
  PostnikovSuccessorClassInverseData.fixedRightDirectCoefficientWitness_native_map
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
