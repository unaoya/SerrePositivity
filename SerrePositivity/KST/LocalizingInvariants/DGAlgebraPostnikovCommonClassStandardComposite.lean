module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonClassStandardFirstComparison
public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightViaAZeroComposition

/-!
概要：元の native 標準像と fⱼ の class 自然性の合成を、零底 ViaA 全体へ同定する。
方針：証明済み全射で第一経路を表示し直し、底付き移送の合成保存を使う。
規約：元の Γ・端点・標準経路の全射を保持。使われ方：fixed 右 class 三角形。
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

def postnikovCommonClassStandardContourRelative :=
  ((postnikovCommonRightViaAFirstZeroPath R f c d hj).mapOver
    (postnikovCommonRightClassifyingBase R f c d hj)
    (SquareZero.baseChangeMap (postnikovCommonRightClassifyingBase R f c d hj)
      (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1))
    (SquareZero.baseChangeMap_projection _ _)).replaceHom
    (postnikovCommonClassFixedStandardMappedRelative R f c d hj).hom
    (postnikovCommonClassFixedStandardMapped_first_hom R f c d hj).symm

def postnikovCommonClassStandardThenNaturality :=
  (postnikovCommonClassStandardContourRelative R f c d hj).comp
    ((postnikovCommonRightViaASecondZeroPath R f c d hj).mapOver
      (postnikovCommonRightClassifyingBase R f c d hj)
      (SquareZero.baseChangeMap (postnikovCommonRightClassifyingBase R f c d hj)
        (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1))
      (SquareZero.baseChangeMap_projection _ _))

lemma postnikovCommonClassStandardThenNaturality_hom :
    (postnikovCommonClassStandardThenNaturality R f c d hj).hom =
    (postnikovCommonRightZeroAffineViaA R f c d hj).hom ≫ Path.map R
      (SquareZero.baseChangeMap (postnikovCommonRightClassifyingBase R f c d hj)
        (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1)) := by
  let k := SquareZero.baseChangeMap (postnikovCommonRightClassifyingBase R f c d hj)
    (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1)
  have hm := SquareZero.RelativeWitness.mapOver_comp_hom
    (postnikovCommonRightClassifyingBase R f c d hj) k
    (SquareZero.baseChangeMap_projection _ _)
    (postnikovCommonRightViaAFirstZeroPath R f c d hj)
    (postnikovCommonRightViaASecondZeroPath R f c d hj)
  have hp := congrArg (fun t => t ≫ Path.map R k)
    (postnikovCommonRightZeroAffineViaA_pair_hom R f c d hj)
  let w := (postnikovCommonRightViaASecondZeroPath R f c d hj).mapOver
    (postnikovCommonRightClassifyingBase R f c d hj) k
    (SquareZero.baseChangeMap_projection _ _)
  have hc := SquareZero.RelativeWitness.replaceHom_comp_hom
    ((postnikovCommonRightViaAFirstZeroPath R f c d hj).mapOver
      (postnikovCommonRightClassifyingBase R f c d hj) k
      (SquareZero.baseChangeMap_projection _ _)) w
    (postnikovCommonClassFixedStandardMappedRelative R f c d hj).hom
    (postnikovCommonClassFixedStandardMapped_first_hom R f c d hj).symm
  exact hc.trans (hm.symm.trans hp.symm)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
