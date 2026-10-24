module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreClassFixedRightZeroSquare
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeSquarePrecomp

/-!
概要：native fixed class の零底射を、元の P 上の classifying 底射へ厳密に同定する。
方針：A 遷移と fⱼ の零切断自然性、元の二因子分解の可換式を使う。
規約：Γ 射影の前合成だけの一致で代用しない。使われ方：二重経路の元の底への復元。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
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

lemma postnikovCommonClassFixedZeroBase_classifying :
    postnikovCommonClassFixedZeroBase R hn f c d hj =
      postnikovCommonRightClassifyingBase R hn f c d hj := by
  rw [← postnikovCommonRightComposite_zero_base R hn f c d hj]
  simp only [postnikovCommonClassFixedZeroBase, postnikovCommonClassRetractBase,
    postnikovCommonRightNaturalityComposite, postnikovMap_composition, Category.assoc]
  rw [postnikovTransition_naturality R (A.obj j).obj (f.app j).hom n 0 (by omega)]

lemma postnikovCommonClassFixedZeroBase_projection :
    postnikovCommonClassStandardGlueProjection R hn f c d ≫
      postnikovCommonClassFixedZeroBase R hn f c d hj =
    postnikovCommonClassStandardGlueProjection R hn f c d ≫
      postnikovCommonRightClassifyingBase R hn f c d hj :=
  congrArg (fun k => postnikovCommonClassStandardGlueProjection R hn f c d ≫ k)
    (postnikovCommonClassFixedZeroBase_classifying R hn f c d hj)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
