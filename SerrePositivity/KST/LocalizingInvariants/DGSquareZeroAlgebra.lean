module

public import SerrePositivity.KST.LocalizingInvariants.SquareZeroUnitLaws
public import SerrePositivity.KST.LocalizingInvariants.CochainTensorBiproductTripleExt
public import SerrePositivity.KST.LocalizingInvariants.TensorTripleComposition

/-!
概要：実 dg 双加群から、分裂平方零 dg 代数を構成する。
方針：三重 tensor の八成分で結合則を証明し、元の左右作用の三則へ戻す。
規約：積の可換性や平坦性を仮定しない。使われ方：derivation による拡大の分類。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalPreadditive Preadditive
open scoped MonObj
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZero
variable {R : Type u} [CommRing R] (A : Mon (Complex R)) (M : Bimod A A)

lemma mul_assoc : (_root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.mul A M ▷ _root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.obj A M) ≫ _root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.mul A M =
    (α_ (_root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.obj A M) (_root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.obj A M) (_root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.obj A M)).hom ≫ (_root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.obj A M ◁ _root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.mul A M) ≫ _root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.mul A M := by
  apply cochainBiprodTensorPairLeft_hom_ext <;> apply biprodTensorRight_hom_ext
  all_goals
    simp only [← tensorHom_def'_assoc, tensorTriple_mul_left, tensorTriple_mul_right,
      _root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.mul_ll, _root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.mul_lr, _root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.mul_rl, _root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.mul_rr, ← whiskerRight_comp_tensorHom_assoc,
      ← whiskerLeft_comp_tensorHom_assoc, _root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.mul_ll_assoc, _root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.mul_lr_assoc, _root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.mul_rl_assoc,
      _root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.mul_rr_assoc, zero_tensor, tensor_zero, zero_comp, comp_zero,
      MonObj.mul_assoc_assoc, M.left_assoc_assoc, M.middle_assoc_assoc,
      M.right_assoc_assoc, Category.assoc, Iso.hom_inv_id_assoc]

/-- 分裂平方零拡大の実非可換 dg 代数。 -/
def algebra : Mon (Complex R) where
  X := _root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.obj A M
  mon := {
    one := _root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.one A M
    mul := _root_.SerrePositivity.InfinityCategories.HA.Section7_3_4.mul A M
    one_mul := one_mul A M
    mul_one := mul_one A M
    mul_assoc := mul_assoc A M }

end SerrePositivity.KST.LocalizingInvariants.SquareZero
