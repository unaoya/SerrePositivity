module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoFixedRightCoefficientModel
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeHomProjections

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSuccessorFixedRightCoefficientPath

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
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} {f : LevelHom A B}
  {j : ℕ} (d : PostnikovTwoClassInverseData R f j)

lemma fixedRightCoefficientWitness_zero_map :
    (d.fixedRightCoefficientWitness R).hom ≫ Path.map R
      (SquareZero.baseChangeMap
        (postnikovCommonRightClassifyingBase R f d.baseInverse d.layerInverse d.target_le)
        (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1)) =
    (postnikovCommonClassFixedCompatibilityMappedRelative R f d.baseInverse d.layerInverse
      d.target_le d.inverse).hom :=
  PostnikovSuccessorClassInverseData.fixedRightCoefficientWitness_zero_map
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
