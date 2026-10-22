module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonClassFixedRightZeroSquare
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
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (postnikovFunctor R 1)) i m hi)
  (d : PostnikovCommonLayerInverse R f c) {j : ℕ} (hj : j ≤ i)

lemma postnikovCommonClassFixedZeroBase_classifying :
    postnikovCommonClassFixedZeroBase R f c d hj =
      postnikovCommonRightClassifyingBase R f c d hj := by
  rw [← postnikovCommonRightComposite_zero_base R f c d hj]
  simp only [postnikovCommonClassFixedZeroBase, postnikovCommonClassRetractBase,
    postnikovCommonRightNaturalityComposite, postnikovMap_composition, Category.assoc]
  rw [postnikovTransition_naturality R (A.obj j).obj (f.app j).hom 1 0 (by omega)]

lemma postnikovCommonClassFixedZeroBase_projection :
    postnikovCommonClassStandardGlueProjection R f c d ≫
      postnikovCommonClassFixedZeroBase R f c d hj =
    postnikovCommonClassStandardGlueProjection R f c d ≫
      postnikovCommonRightClassifyingBase R f c d hj :=
  congrArg (fun k => postnikovCommonClassStandardGlueProjection R f c d ≫ k)
    (postnikovCommonClassFixedZeroBase_classifying R f c d hj)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
