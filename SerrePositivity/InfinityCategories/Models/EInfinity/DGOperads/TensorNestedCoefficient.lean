module

public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.Tactic.CategoryTheory.Monoidal.Basic

/-!
模型。文献の定義との比較は後で
# 外側の係数を保つ二段のテンソル射

概要：Berger–Moerdijk §1 の二段の全合成で、外側の係数と内側の係数を分けて計算する。
方針：結合子の整合性と自然性で内側の係数射と入力射を独立に動かす。
規約：対象の交換は加えず、入力の順序を保つ。
使われ方：Schur 演算の係数側と入力側の結合則を一つのテンソル射にまとめる。
-/

@[expose] public section

universe v u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory

variable {C₀ : Type u} [Category.{v} C₀] [MonoidalCategory C₀]

/-- 概要：外側と内側の係数を含む四因子の括弧の移動は整合する（Berger–Moerdijk §1）。
方針：結合子の pentagon による整合性を使う。
規約：R,S,D,E の順序を保存する。
使われ方：二段の演算の係数を右括弧でまとめる。 -/
@[reassoc]
lemma tensorNestedCoefficient_coherence (R S D E : C₀) :
    (α_ R S (D ⊗ E)).hom ≫ (R ◁ (α_ S D E).inv) ≫ (α_ R (S ⊗ D) E).inv =
      (α_ (R ⊗ S) D E).inv ≫ ((α_ R S D).hom ▷ E) := by
  monoidal

/-- 概要：二段の係数・入力のテンソル射を係数の二段の合成と入力の合成へまとめる（Berger–Moerdijk §1）。
方針：内側の射を結合子の自然性で移し、四因子の整合性とテンソル射の合成則を使う。
規約：a は入力族から係数列と入力列への分離射。
使われ方：内側の Schur 演算の後の外側の演算を独立な係数側と入力側へ分ける。 -/
lemma tensorNestedCoefficient {R S D E D' E' O L V : C₀}
    (a : V ⟶ D ⊗ E) (f : S ⊗ D ⟶ D') (g : E ⟶ E')
    (h : R ⊗ D' ⟶ O) (k : E' ⟶ L) :
    (α_ R S V).hom ≫
      (R ◁ ((S ◁ a) ≫ (α_ S D E).inv ≫ (f ⊗ₘ g))) ≫
      (α_ R D' E').inv ≫ (h ⊗ₘ k) =
    ((R ⊗ S) ◁ a) ≫ (α_ (R ⊗ S) D E).inv ≫
      (((α_ R S D).hom ≫ (R ◁ f) ≫ h) ⊗ₘ (g ≫ k)) := by
  simp only [whiskerLeft_comp, Category.assoc]
  rw [← associator_naturality_right_assoc]
  have hn := associator_inv_naturality (𝟙 R) f g
  simp only [id_tensorHom] at hn
  rw [reassoc_of% hn, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorNestedCoefficient_coherence_assoc,
    whiskerRight_comp_tensorHom_assoc, tensorHom_comp_tensorHom]
  simp only [Category.assoc]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
