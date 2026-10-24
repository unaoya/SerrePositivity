module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreClassFixedBaseNormalization
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightDenDirectData

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
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
open ProExcision
variable (R : Type u) [CommRing R] {n : ℤ} (hn : 0 ≤ n)
  {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (lowerFunctor R n hn)) i m hi)
  (d : PostnikovCommonLayerInverse R hn f c) {j : ℕ} (hj : j ≤ i)

attribute [local instance] PostnikovRoofZeroSpan.refined_source_nonpositive
  PostnikovRoofZeroSpan.refined_target_nonpositive

def postnikovCommonClassRightImageBase :=
  postnikovCommonClassRetractBase R hn f c d (hj := hj) ≫ postnikovMap R (f.app j).hom n

lemma postnikovCommonClassRightImageBase_zero :
    postnikovCommonClassRightImageBase R hn f c d hj ≫
      postnikovTransition R (B.obj j).obj n 0 (by omega) =
    postnikovCommonRightClassifyingBase R hn f c d hj := by
  rw [postnikovCommonClassRightImageBase, Category.assoc,
    postnikovTransition_naturality R (A.obj j).obj (f.app j).hom n 0 (by omega)]
  exact postnikovCommonClassFixedZeroBase_classifying R hn f c d hj

def postnikovCommonClassRightDenominatorBase :=
  (roofRefine R hn f c d.zero.source_le).roof.denominator ≫
    postnikovMap R (postnikovCommonRightDenDirectMap R hn f c d hj) n

lemma postnikovCommonClassRightDenominatorBase_zero :
    postnikovCommonClassRightDenominatorBase R hn f c d hj ≫
      postnikovTransition R (B.obj j).obj n 0 (by omega) =
    postnikovCommonRightClassifyingBase R hn f c d hj := by
  let h := postnikovCellFactorizationImage_base R (B.obj d.zero.stage).obj (B.obj j).obj
    (postnikovCommonClassBase R hn f c d) n
    (roofRefine R hn f c d.zero.source_le).roof.denominator
    (postnikovCommonRightDenDirectMap R hn f c d hj) (B.obj i).obj
    (B.transition (d.zero.inverse_le.trans d.zero.stage_le)).hom (B.transition hj).hom
    (postnikovCommonRightDenDirect_factorization R hn f c d hj)
  let k := congrArg (fun b => b ≫ postnikovTransition R (B.obj j).obj n 0 (by omega)) h
  exact k.trans (postnikovCommonRightDenComposite_zero_base R hn f c d hj)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
