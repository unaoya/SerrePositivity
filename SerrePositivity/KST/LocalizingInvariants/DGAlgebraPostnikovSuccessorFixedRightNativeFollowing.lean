module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSuccessorFixedRightDirectCoefficientModel
public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreClassFixedRightRestored

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
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovSuccessorClassInverseData
open ProExcision
variable (R : Type u) [CommRing R] {n : ℤ} {hn : 0 ≤ n} {A B : Tower (NonpositiveAlgebra R)} {f : LevelHom A B}
  {j : ℕ} (d : PostnikovSuccessorClassInverseData R hn f j)

def fixedRightNativeCompatibility :=
  (PostnikovCommonCore.postnikovCommonClassFixedCompatibilityMappedRelative R hn f d.baseInverse d.layerInverse
    d.target_le d.inverse).rebase
      (PostnikovCommonCore.postnikovCommonClassFixedZeroBase_projection R hn f d.baseInverse d.layerInverse d.target_le)

def fixedRightNativeFollowing :=
  ((PostnikovCommonCore.postnikovCommonClassFixedRightNaturality R hn f d.baseInverse d.layerInverse d.target_le).comp
    (PostnikovCommonCore.postnikovCommonClassFixedRightBottom R hn f d.baseInverse d.layerInverse d.target_le
      d.inverse)).rebase
        (PostnikovCommonCore.postnikovCommonClassFixedZeroBase_projection R hn f d.baseInverse d.layerInverse d.target_le)

lemma fixedRightNativeCompatibility_hom : (d.fixedRightNativeCompatibility R).hom =
    (PostnikovCommonCore.postnikovCommonClassFixedCompatibilityMappedRelative R hn f d.baseInverse d.layerInverse
      d.target_le d.inverse).hom := SquareZero.RelativeWitness.rebase_hom _ _

lemma fixedRightNativeFollowing_comp_hom :
    ((d.fixedRightNativeCompatibility R).comp (d.fixedRightNativeFollowing R)).hom =
    (PostnikovCommonCore.postnikovCommonClassFixedRightCompletedPath R hn f d.baseInverse d.layerInverse
      d.target_le d.inverse).hom := by
  let v := PostnikovCommonCore.postnikovCommonClassFixedCompatibilityMappedRelative R hn f d.baseInverse
    d.layerInverse d.target_le d.inverse
  let w := PostnikovCommonCore.postnikovCommonClassFixedRightNaturality R hn f d.baseInverse d.layerInverse d.target_le
  let z := PostnikovCommonCore.postnikovCommonClassFixedRightBottom R hn f d.baseInverse d.layerInverse d.target_le
    d.inverse
  let h := SquareZero.RelativeWitness.comp_congr_hom_of_paths
    (v := d.fixedRightNativeCompatibility R) (w := d.fixedRightNativeFollowing R)
    (v' := v) (w' := w.comp z) (d.fixedRightNativeCompatibility_hom R)
    (SquareZero.RelativeWitness.rebase_hom (w.comp z)
      (PostnikovCommonCore.postnikovCommonClassFixedZeroBase_projection R hn f d.baseInverse d.layerInverse d.target_le))
  exact h.trans (SquareZero.RelativeWitness.comp_assoc_hom v w z).symm

lemma fixedRightDirectCoefficientWitness_native_map :
    (d.fixedRightDirectCoefficientWitness R).hom ≫ Path.map R
      (SquareZero.baseChangeMap
        (PostnikovCommonCore.postnikovCommonRightClassifyingBase R hn f d.baseInverse d.layerInverse d.target_le)
        (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj n) 1)) =
    (d.fixedRightNativeCompatibility R).hom :=
  (d.fixedRightDirectCoefficientWitness_zero_map R).trans
    (d.fixedRightNativeCompatibility_hom R).symm

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovSuccessorClassInverseData
