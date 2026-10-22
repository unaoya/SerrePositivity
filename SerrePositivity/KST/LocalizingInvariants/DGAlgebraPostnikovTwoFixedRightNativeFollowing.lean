module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoFixedRightDirectCoefficientModel
public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonClassFixedRightRestored

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
  (postnikovCommonClassFixedCompatibilityMappedRelative R f d.baseInverse d.layerInverse
    d.target_le d.inverse).rebase
      (postnikovCommonClassFixedZeroBase_projection R f d.baseInverse d.layerInverse d.target_le)

def fixedRightNativeFollowing :=
  ((postnikovCommonClassFixedRightNaturality R f d.baseInverse d.layerInverse d.target_le).comp
    (postnikovCommonClassFixedRightBottom R f d.baseInverse d.layerInverse d.target_le
      d.inverse)).rebase
        (postnikovCommonClassFixedZeroBase_projection R f d.baseInverse d.layerInverse d.target_le)

lemma fixedRightNativeCompatibility_hom : (d.fixedRightNativeCompatibility R).hom =
    (postnikovCommonClassFixedCompatibilityMappedRelative R f d.baseInverse d.layerInverse
      d.target_le d.inverse).hom := SquareZero.RelativeWitness.rebase_hom _ _

lemma fixedRightNativeFollowing_comp_hom :
    ((d.fixedRightNativeCompatibility R).comp (d.fixedRightNativeFollowing R)).hom =
    (postnikovCommonClassFixedRightCompletedPath R f d.baseInverse d.layerInverse
      d.target_le d.inverse).hom := by
  let v := postnikovCommonClassFixedCompatibilityMappedRelative R f d.baseInverse
    d.layerInverse d.target_le d.inverse
  let w := postnikovCommonClassFixedRightNaturality R f d.baseInverse d.layerInverse d.target_le
  let z := postnikovCommonClassFixedRightBottom R f d.baseInverse d.layerInverse d.target_le
    d.inverse
  let h := SquareZero.RelativeWitness.comp_congr_hom_of_paths
    (v := d.fixedRightNativeCompatibility R) (w := d.fixedRightNativeFollowing R)
    (v' := v) (w' := w.comp z) (d.fixedRightNativeCompatibility_hom R)
    (SquareZero.RelativeWitness.rebase_hom (w.comp z)
      (postnikovCommonClassFixedZeroBase_projection R f d.baseInverse d.layerInverse d.target_le))
  exact h.trans (SquareZero.RelativeWitness.comp_assoc_hom v w z).symm

lemma fixedRightDirectCoefficientWitness_native_map :
    (d.fixedRightDirectCoefficientWitness R).hom ≫ Path.map R
      (SquareZero.baseChangeMap
        (postnikovCommonRightClassifyingBase R f d.baseInverse d.layerInverse d.target_le)
        (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1)) =
    (d.fixedRightNativeCompatibility R).hom :=
  (d.fixedRightDirectCoefficientWitness_zero_map R).trans
    (d.fixedRightNativeCompatibility_hom R).symm

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
