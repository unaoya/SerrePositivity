module

public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.Tactic.CategoryTheory.Monoidal.Basic

/-!
模型。文献の定義との比較は後で
# 単位係数列を縮約したテンソル射

概要：Berger–Moerdijk §1 の全合成の右単位則で、係数列の縮約を入力側の左単位子へ移す。
方針：結合子の自然性、テンソル射の交換則、単位子の整合性を使う。
規約：係数の後続射 q と入力の射 g は独立。
使われ方：単位演算を各入力に入れた Schur 演算を通常の生成射へ戻す。
-/

@[expose] public section

universe v u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory

variable {C₀ : Type u} [Category.{v} C₀] [MonoidalCategory C₀]

/-- 概要：縮約した単位係数の作用は入力側の左単位子の適用に一致する（Berger–Moerdijk §1）。
方針：係数射を入力射の後へ移し、結合子と右単位子を入力側の左単位子へまとめる。
規約：最後の評価射 r の終域は任意。
使われ方：全合成の右単位則の係数計算を Schur 生成射に送る。 -/
lemma tensorUnitCoefficient {C O U W Z Y : C₀} (a : U ⟶ 𝟙_ C₀) (q : C ⟶ O)
    (g : W ⟶ Z) (r : O ⊗ Z ⟶ Y) :
    (α_ C U W).inv ≫ (((C ◁ a) ≫ (ρ_ C).hom ≫ q) ⊗ₘ g) ≫ r =
    (C ◁ ((a ⊗ₘ 𝟙 W) ≫ (λ_ W).hom ≫ g)) ≫ (q ▷ Z) ≫ r := by
  simp only [tensorHom_def, comp_whiskerRight, Category.assoc]
  rw [← whisker_exchange_assoc q g, ← associator_inv_naturality_middle_assoc]
  have h : (α_ C (𝟙_ C₀) W).inv ≫ ((ρ_ C).hom ▷ W) = C ◁ (λ_ W).hom := by
    monoidal_coherence
  rw [reassoc_of% h]
  simp only [whiskerLeft_comp, whiskerLeft_id, Category.id_comp, Category.assoc]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
