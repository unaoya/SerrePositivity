module

public import Mathlib.CategoryTheory.Monoidal.Category

/-!
模型。文献の定義との比較は後で
# 末尾入力を保つ係数と入力の分離の自然性

概要：Berger–Moerdijk §1 の反復合成で係数列と入力列の射を末尾入力付きの分離へ通す。
方針：二つの結合子の自然性とテンソル射の合成則を使う。
規約：末尾 T は固定し、係数列と入力列の射を独立に扱う。
使われ方：有限族の末尾分離の逆射を係数の合成と入力の連結に移す。
-/

@[expose] public section

universe v u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory

variable {C₀ : Type u} [Category.{v} C₀] [MonoidalCategory C₀]

/-- 概要：係数と入力の二列の射は末尾入力を含む分離を通して合成へ移せる（Berger–Moerdijk §1）。
方針：二つの結合子の自然性で射を後へ移し、独立なテンソル射の合成をまとめる。
規約：始域と終域の係数列・入力列の括弧付けを別々に指定する。
使われ方：末尾を残した反復合成を最後の演算に沿って分解する。 -/
@[reassoc]
lemma tensorTailSeparation_naturality {R V W V' W' T O U : C₀}
    (v : V ⟶ V') (w : W ⟶ W') (f : R ⊗ V' ⟶ O) (g : W' ⊗ T ⟶ U) :
    (R ◁ ((v ⊗ₘ w) ▷ T)) ≫ (R ◁ (α_ V' W' T).hom) ≫
      (α_ R V' (W' ⊗ T)).inv ≫ (f ⊗ₘ g) =
    (R ◁ (α_ V W T).hom) ≫ (α_ R V (W ⊗ T)).inv ≫
      (((R ◁ v) ≫ f) ⊗ₘ ((w ▷ T) ≫ g)) := by
  have h₁ := associator_naturality v w (𝟙 T)
  simp only [tensorHom_id] at h₁
  have h₂ := associator_inv_naturality (𝟙 R) v (w ▷ T)
  simp only [id_tensorHom] at h₂
  rw [← whiskerLeft_comp_assoc, h₁]
  simp only [whiskerLeft_comp, Category.assoc]
  rw [reassoc_of% h₂, tensorHom_comp_tensorHom]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
