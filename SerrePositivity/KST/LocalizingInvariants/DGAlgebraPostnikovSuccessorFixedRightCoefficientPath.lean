module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSuccessorFixedRightCoefficientModel
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeHomProjections

/-!
概要：fixed の元の模型合成が使う class 経路の零 class 像を、元の native 経路へ同定。
方針：係数後合成の全経路式と、fⱼ 係数射の元の零 class 射への厳密な式を使う。
規約：sourceToTargetFixedRelative の元の class 経路を保持。使われ方：実右模型三角形。
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

lemma fixedRightCoefficientWitness_zero_map :
    (d.fixedRightCoefficientWitness R).hom ≫ Path.map R
      (SquareZero.baseChangeMap
        (PostnikovCommonCore.postnikovCommonRightClassifyingBase R hn f d.baseInverse d.layerInverse d.target_le)
        (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj n) 1)) =
    (PostnikovCommonCore.postnikovCommonClassFixedCompatibilityMappedRelative R hn f d.baseInverse d.layerInverse
      d.target_le d.inverse).hom := by
  let q := PostnikovCommonCore.postnikovCommonRightClassifyingBase R hn f d.baseInverse d.layerInverse d.target_le
  let N := DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj n) 1
  let h := SquareZeroExtension.postCoefficientClassWitness_post (d.classCoefficient R)
    (d.rightTargetCoefficient R) (d.sourceClass R) (d.targetClass R)
    (d.classFixedRelativeWitness R) (SquareZero.baseChangeMap q N)
  let k := congrArg (fun t => (d.classFixedRelativeWitness R).hom ≫ Path.map R t)
    (d.rightTargetCoefficient_zero_map R)
  let g := congrArg (fun t => t ≫ Path.map R
    (PostnikovCommonCore.postnikovCommonClassFixedZeroMap R hn f d.baseInverse d.layerInverse d.target_le))
    (d.classFixedRelativeWitness_hom R)
  let t := SquareZero.RelativeWitness.mapOver_hom
    (PostnikovCommonCore.postnikovCommonClassFixedGlueCompatibility R hn f d.baseInverse d.layerInverse d.inverse)
    (PostnikovCommonCore.postnikovCommonClassFixedZeroBase R hn f d.baseInverse d.layerInverse d.target_le)
    (PostnikovCommonCore.postnikovCommonClassFixedZeroMap R hn f d.baseInverse d.layerInverse d.target_le)
    (PostnikovCommonCore.postnikovCommonClassFixedZeroMap_projection R hn f d.baseInverse d.layerInverse d.target_le)
  exact ((h.trans k).trans g).trans t.symm

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovSuccessorClassInverseData
