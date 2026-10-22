module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovClassZeroRebaseIso
public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightContourLeftComparison

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
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (postnikovFunctor R 1)) i m hi)
  (d : PostnikovCommonLayerInverse R f c) {j : ℕ} (hj : j ≤ i)

def postnikovCommonRightDenCompositeBase :=
  postnikovCommonRightDenBase R f c d ≫ postnikovMap R (B.transition hj).hom 1

lemma postnikovCommonRightDenComposite_zero_base :
    postnikovCommonRightDenCompositeBase R f c d hj ≫
      postnikovTransition R (B.obj j).obj 1 0 (by omega) =
      postnikovCommonRightClassifyingBase R f c d hj := by
  rw [postnikovCommonRightDenCompositeBase, Category.assoc, postnikovTransition_naturality,
    ← Category.assoc, ← postnikovCommonRightZeroBase_den R f c d]
  exact (postnikovCommonRightClassifyingBase_zero R f c d hj).symm

def postnikovCommonRightDenCompositeZeroIso :=
  postnikovClassZeroRebaseIso R (B.obj j).obj (postnikovCommonClassBase R f c d)
    1 (by omega) 1 (postnikovCommonRightDenCompositeBase R f c d hj)
    (postnikovCommonRightClassifyingBase R f c d hj)
    (postnikovCommonRightDenComposite_zero_base R f c d hj)

lemma postnikovCommonRightDenCompositeZeroIso_projection :
    (postnikovCommonRightDenCompositeZeroIso R f c d hj).hom ≫
      SquareZero.projection _ _ = SquareZero.projection _ _ :=
  postnikovClassZeroRebaseIso_projection R (B.obj j).obj (postnikovCommonClassBase R f c d)
    1 (by omega) 1 _ _ (postnikovCommonRightDenComposite_zero_base R f c d hj)

lemma postnikovCommonRightDenCompositeZeroIso_map :
    (postnikovCommonRightDenCompositeZeroIso R f c d hj).hom ≫
      SquareZero.baseChangeMap (postnikovCommonRightClassifyingBase R f c d hj)
        (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1) =
    SquareZero.baseChangeMap (postnikovCommonRightDenCompositeBase R f c d hj)
      (postnikovShiftedLayerBimodule R (B.obj j).obj 1 (by omega) 1) ≫
      postnikovClassToZeroBase R (B.obj j).obj 1 (by omega) 1 :=
  postnikovClassZeroRebaseIso_map R (B.obj j).obj (postnikovCommonClassBase R f c d)
    1 (by omega) 1 _ _ (postnikovCommonRightDenComposite_zero_base R f c d hj)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
