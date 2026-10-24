module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovClassZeroRebaseIso
public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightContourLeftComparison

/-!
概要：元の分母の二段 B 遷移の係数を、同じ classifying 零底係数へ移す。
方針：元の DenBase の零切断式と Postnikov 遷移の自然性を使う。
規約：分子と同じ Γ 射影・零底を保持。使われ方：S′R の二自然性経路との照合。
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

def postnikovCommonRightDenCompositeBase :=
  postnikovCommonRightDenBase R hn f c d ≫ postnikovMap R (B.transition hj).hom n

lemma postnikovCommonRightDenComposite_zero_base :
    postnikovCommonRightDenCompositeBase R hn f c d hj ≫
      postnikovTransition R (B.obj j).obj n 0 (by omega) =
      postnikovCommonRightClassifyingBase R hn f c d hj := by
  rw [postnikovCommonRightDenCompositeBase, Category.assoc, postnikovTransition_naturality,
    ← Category.assoc, ← postnikovCommonRightZeroBase_den R hn f c d]
  exact (postnikovCommonRightClassifyingBase_zero R hn f c d hj).symm

def postnikovCommonRightDenCompositeZeroIso :=
  postnikovClassZeroRebaseIso R (B.obj j).obj (postnikovCommonClassBase R hn f c d)
    n hn 1 (postnikovCommonRightDenCompositeBase R hn f c d hj)
    (postnikovCommonRightClassifyingBase R hn f c d hj)
    (postnikovCommonRightDenComposite_zero_base R hn f c d hj)

lemma postnikovCommonRightDenCompositeZeroIso_projection :
    (postnikovCommonRightDenCompositeZeroIso R hn f c d hj).hom ≫
      SquareZero.projection _ _ = SquareZero.projection _ _ :=
  postnikovClassZeroRebaseIso_projection R (B.obj j).obj (postnikovCommonClassBase R hn f c d)
    n hn 1 _ _ (postnikovCommonRightDenComposite_zero_base R hn f c d hj)

lemma postnikovCommonRightDenCompositeZeroIso_map :
    (postnikovCommonRightDenCompositeZeroIso R hn f c d hj).hom ≫
      SquareZero.baseChangeMap (postnikovCommonRightClassifyingBase R hn f c d hj)
        (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj n) 1) =
    SquareZero.baseChangeMap (postnikovCommonRightDenCompositeBase R hn f c d hj)
      (postnikovShiftedLayerBimodule R (B.obj j).obj n hn 1) ≫
      postnikovClassToZeroBase R (B.obj j).obj n hn 1 :=
  postnikovClassZeroRebaseIso_map R (B.obj j).obj (postnikovCommonClassBase R hn f c d)
    n hn 1 _ _ (postnikovCommonRightDenComposite_zero_base R hn f c d hj)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
