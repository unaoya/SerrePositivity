module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoFixedRightNativeFollowing
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeBaseChangeFollowing
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeClassPostTransport

/-!
概要：元の fixed 模型射の係数後合成に、fⱼ 自然性と W の実輸送を接合する。
方針：元の全 class 経路像で接合端点を回収し、同じ P への実底変更 lift を使う。
規約：元の実模型合成を保持。使われ方：直接分母模型射との実右三角形比較。
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

def fixedRightFollowingWitness := SquareZero.baseChangeFollowingWitness
  (postnikovCommonRightClassifyingBase R f d.baseInverse d.layerInverse d.target_le)
  (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1)
  (postnikovCommonClassStandardGlueProjection R f d.baseInverse d.layerInverse)
  (d.fixedRightDirectCoefficientWitness R) (d.fixedRightNativeCompatibility R)
  (d.fixedRightDirectCoefficientWitness_native_map R) (d.fixedRightNativeFollowing R)

def fixedRightCompletedWitness :=
  (d.fixedRightDirectCoefficientWitness R).comp (d.fixedRightFollowingWitness R)

lemma fixedRightCompletedWitness_zero_map : (d.fixedRightCompletedWitness R).hom ≫ Path.map R
    (SquareZero.baseChangeMap
      (postnikovCommonRightClassifyingBase R f d.baseInverse d.layerInverse d.target_le)
      (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1)) =
    (postnikovCommonClassFixedRightCompletedPath R f d.baseInverse d.layerInverse
      d.target_le d.inverse).hom := by
  let h := SquareZero.baseChangeFollowingWitness_comp_map
    (postnikovCommonRightClassifyingBase R f d.baseInverse d.layerInverse d.target_le)
    (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1)
    (postnikovCommonClassStandardGlueProjection R f d.baseInverse d.layerInverse)
    (d.fixedRightDirectCoefficientWitness R) (d.fixedRightNativeCompatibility R)
    (d.fixedRightDirectCoefficientWitness_native_map R) (d.fixedRightNativeFollowing R)
  exact h.trans (d.fixedRightNativeFollowing_comp_hom R)

def sourceToRightCompletedModel := d.sourceToRightCoefficientModel R ≫
  SquareZeroExtension.transport (d.rightClassifyingLayer R) (d.fixedRightFollowingWitness R)

lemma sourceToRightCompletedModel_eq : d.sourceToRightCompletedModel R =
    SquareZeroExtension.classModelMap (d.rightDenominatorCoefficient R) (d.sourceClass R) _
      (d.fixedRightCompletedWitness R) := by
  let h := congrArg (fun t => t ≫ SquareZeroExtension.transport
    (d.rightClassifyingLayer R) (d.fixedRightFollowingWitness R))
    (d.sourceToRightCoefficientModel_eq_direct R)
  exact h.trans (SquareZeroExtension.classModelMap_postTransport
    (d.rightDenominatorCoefficient R) (d.sourceClass R) (d.rightImageClass R) _
    (d.fixedRightDirectCoefficientWitness R) (d.fixedRightFollowingWitness R))

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
