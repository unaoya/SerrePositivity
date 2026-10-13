module

public import SerrePositivity.CategoryTheory.Monoidal.TensorPowerBlockGenerators

/-! # 反復テンソルの先頭因子を末尾へ移す

隣接交換の再帰を、braidingのhexagonと連結同型を用いた射として比較する。
このモジュールは置換作用や球面に依存しない。
-/

@[expose] public section

universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.TensorPowers

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- 隣接交換の再帰で先頭の因子を末尾へ送る同型。 -/
def moveFirstIso (X : C) : ∀ n, power X (n + 1) ≅ power X (n + 1)
  | 0 => Iso.refl _
  | n + 1 => swapFirstIso X n ≪≫ whiskerLeftIso X (moveFirstIso X n)
/-- 隣接交換の列は、braidingと尾への連結による射に一致する。 -/
lemma moveFirstIso_braiding (X : C) (n : ℕ) :
    (moveFirstIso X n).hom =
      (β_ X (power X n)).hom ≫ (power X n ◁ (ρ_ X).inv) ≫ (appendIso X n 1).hom := by
  induction n with
  | zero =>
    simp only [moveFirstIso, Iso.refl_hom, power, appendIso, Iso.trans_hom,
      eqToIso.hom, eqToHom_refl, Category.comp_id]
    rw [leftUnitor_naturality, braiding_leftUnitor_assoc, Iso.hom_inv_id]
  | succ n ih =>
    simp only [moveFirstIso, Iso.trans_hom, whiskerLeftIso_hom, ih]
    simp only [power, appendIso, Iso.trans_hom, whiskerLeftIso_hom,
      eqToIso.hom, eqToHom_refl, Category.comp_id]
    rw [braiding_tensor_right_hom]
    simp only [Category.assoc]
    erw [associator_naturality_right_assoc]
    simp only [Iso.inv_hom_id_assoc]
    simp only [swapFirstIso, Iso.trans_hom, Iso.symm_hom, whiskerRightIso_hom,
      whiskerLeft_comp, Category.assoc]

/-- 第1段と尾のbraidingの後の連結は、巡回移動の前に右単位子を適用した射。 -/
@[reassoc] lemma oneCrossing_comparison (X : C) (n : ℕ) :
    (β_ (power X 1) (power X n)).hom ≫ (appendIso X n 1).hom =
      ((ρ_ X).hom ▷ power X n) ≫ (moveFirstIso X n).hom := by
  rw [moveFirstIso_braiding]
  erw [braiding_naturality_left_assoc]
  simp only [← whiskerLeft_comp_assoc, Iso.hom_inv_id, whiskerLeft_id, Category.id_comp]
  rfl
end SerrePositivity.TensorPowers
