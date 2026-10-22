module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoFixedRightCoefficientPath
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeClassCoefficientChange

/-!
概要：元の fixed 模型射の係数後合成を、元の直接 B 遷移の係数射で厳密に表示する。
方針：実双加群射の三角形で class 証人の源表示だけを移し、元の全射を保持する。
規約：実模型射と native 零 class 像を保持。使われ方：実右逆三角形の模型照合。
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

def fixedRightDirectCoefficientWitness := SquareZeroExtension.changeCoefficientWitness
  (d.classCoefficient R ≫ d.rightTargetCoefficient R) (d.rightDenominatorCoefficient R)
  (d.classCoefficient_right_triangle R) (d.sourceClass R) (d.rightImageClass R)
  (d.fixedRightCoefficientWitness R)

lemma sourceToRightCoefficientModel_eq_direct : d.sourceToRightCoefficientModel R =
    SquareZeroExtension.classModelMap (d.rightDenominatorCoefficient R)
      (d.sourceClass R) (d.rightImageClass R) (d.fixedRightDirectCoefficientWitness R) := by
  let h := SquareZeroExtension.classModelMap_changeCoefficient
    (d.classCoefficient R ≫ d.rightTargetCoefficient R) (d.rightDenominatorCoefficient R)
    (d.classCoefficient_right_triangle R) (d.sourceClass R) (d.rightImageClass R)
    (d.fixedRightCoefficientWitness R)
  exact (d.sourceToRightCoefficientModel_eq R).trans h

lemma fixedRightDirectCoefficientWitness_zero_map :
    (d.fixedRightDirectCoefficientWitness R).hom ≫ Path.map R
      (SquareZero.baseChangeMap
        (postnikovCommonRightClassifyingBase R f d.baseInverse d.layerInverse d.target_le)
        (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1)) =
    (postnikovCommonClassFixedCompatibilityMappedRelative R f d.baseInverse d.layerInverse
      d.target_le d.inverse).hom := by
  let h := SquareZeroExtension.changeCoefficientWitness_hom
    (d.classCoefficient R ≫ d.rightTargetCoefficient R) (d.rightDenominatorCoefficient R)
    (d.classCoefficient_right_triangle R) (d.sourceClass R) (d.rightImageClass R)
    (d.fixedRightCoefficientWitness R)
  let k := congrArg (fun t => t ≫ Path.map R
    (SquareZero.baseChangeMap
      (postnikovCommonRightClassifyingBase R f d.baseInverse d.layerInverse d.target_le)
      (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1))) h
  exact k.trans (d.fixedRightCoefficientWitness_zero_map R)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
