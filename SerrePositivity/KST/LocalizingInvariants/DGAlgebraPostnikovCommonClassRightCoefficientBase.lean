module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonClassFixedBaseNormalization
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightDenDirectData

/-!
概要：fⱼ と直接 B 遷移の係数射を、元の P 上の classifying 係数へ移す底射を固定する。
方針：切断の自然性と塔の厳密合成式で、両射の零底を同じ元の底射へ同定する。
規約：P 全体上の等式を保持。使われ方：fixed 模型射の右係数三角形。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (postnikovFunctor R 1)) i m hi)
  (d : PostnikovCommonLayerInverse R f c) {j : ℕ} (hj : j ≤ i)

def postnikovCommonClassRightImageBase :=
  postnikovCommonClassRetractBase R f c d (hj := hj) ≫ postnikovMap R (f.app j).hom 1

lemma postnikovCommonClassRightImageBase_zero :
    postnikovCommonClassRightImageBase R f c d hj ≫
      postnikovTransition R (B.obj j).obj 1 0 (by omega) =
    postnikovCommonRightClassifyingBase R f c d hj := by
  rw [postnikovCommonClassRightImageBase, Category.assoc,
    postnikovTransition_naturality R (A.obj j).obj (f.app j).hom 1 0 (by omega)]
  exact postnikovCommonClassFixedZeroBase_classifying R f c d hj

def postnikovCommonClassRightDenominatorBase :=
  (postnikovOneRoofRefine R f c d.zero.source_le).roof.denominator ≫
    postnikovMap R (postnikovCommonRightDenDirectMap R f c d hj) 1

lemma postnikovCommonClassRightDenominatorBase_zero :
    postnikovCommonClassRightDenominatorBase R f c d hj ≫
      postnikovTransition R (B.obj j).obj 1 0 (by omega) =
    postnikovCommonRightClassifyingBase R f c d hj := by
  let h := postnikovCellFactorizationImage_base R (B.obj d.zero.stage).obj (B.obj j).obj
    (postnikovCommonClassBase R f c d) 1
    (postnikovOneRoofRefine R f c d.zero.source_le).roof.denominator
    (postnikovCommonRightDenDirectMap R f c d hj) (B.obj i).obj
    (B.transition (d.zero.inverse_le.trans d.zero.stage_le)).hom (B.transition hj).hom
    (postnikovCommonRightDenDirect_factorization R f c d hj)
  let k := congrArg (fun b => b ≫ postnikovTransition R (B.obj j).obj 1 0 (by omega)) h
  exact k.trans (postnikovCommonRightDenComposite_zero_base R f c d hj)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
