module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorSeparationBraiding
public import Mathlib.Tactic.CategoryTheory.Monoidal.Basic

/-!
模型。文献の定義との比較は後で
# 係数を含むブロックの合成とテンソル対の分離

概要：Berger–Moerdijk §1 の二段の全合成で、内側の係数を合成する操作をテンソル分離へ通す。
方針：構造射の整合性と tensorμ の自然性を分けて証明する。
規約：外側の係数 C は移動せず、入力 E と後半の係数 F の交換を保持する。
使われ方：先頭ブロックの合成を係数列と入力列で独立に計算する。
-/

@[expose] public section

universe v u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory

variable {C₀ : Type u} [Category.{v} C₀] [MonoidalCategory C₀] [SymmetricCategory C₀]

/-- 概要：先頭の係数を含む括弧の移動はテンソル対の分離と両立する（Berger–Moerdijk §1）。
方針：tensorμ を展開し、結合子の整合性で係数 C を左端に保つ。
規約：二つのテンソル対は D,E と F,G。
使われ方：先頭ブロックの係数を合成する射の自然性を適用する。 -/
@[reassoc]
lemma tensorCoefficientSeparation_coherence (C D E F G : C₀) :
    (α_ C (D ⊗ E) (F ⊗ G)).inv ≫
      ((α_ C D E).inv ▷ (F ⊗ G)) ≫ tensorμ (C ⊗ D) E F G =
    (C ◁ tensorμ D E F G) ≫ (α_ C (D ⊗ F) (E ⊗ G)).inv ≫
      ((α_ C D F).inv ⊗ₘ 𝟙 (E ⊗ G)) := by
  simp only [tensorμ, tensorHom_def]
  monoidal

/-- 概要：先頭ブロックの係数と入力を合成してから分離する計算は独立な二列の計算に等しい（Berger–Moerdijk §1）。
方針：係数と入力の射を tensorμ の自然性で後へ移し、構造射の整合性を使う。
規約：f は係数 C,D の合成、g は入力 E の連結を表す。
使われ方：自由代数の部分合成則で係数側と入力側の結合則を合わせる。 -/
lemma tensorCoefficientSeparation {C D E F G D' E' : C₀}
    (f : C ⊗ D ⟶ D') (g : E ⟶ E') :
    (α_ C (D ⊗ E) (F ⊗ G)).inv ≫
      (((α_ C D E).inv ≫ (f ⊗ₘ g)) ▷ (F ⊗ G)) ≫ tensorμ D' E' F G =
    (C ◁ tensorμ D E F G) ≫ (α_ C (D ⊗ F) (E ⊗ G)).inv ≫
      (((α_ C D F).inv ≫ (f ▷ F)) ⊗ₘ (g ▷ G)) := by
  simp only [comp_whiskerRight, Category.assoc]
  rw [tensorμ_natural_left]
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorCoefficientSeparation_coherence_assoc]
  simp only [tensorHom_comp_tensorHom, Category.id_comp]

/-- 概要：先頭と後半の分離射を通したブロックの合成は二列の独立な計算に等しい（Berger–Moerdijk §1）。
方針：分離射 a,b を結合子の自然性で前へ移し、係数を含む分離の整合性を使う。
規約：a と b は独立な入力ブロックから二列への任意の射。
使われ方：有限入力族の分離同型を先頭ブロックの合成へ通す。 -/
lemma tensorCoefficientSeparation_maps {C D E F G D' E' V W : C₀}
    (a : V ⟶ D ⊗ E) (b : W ⟶ F ⊗ G) (f : C ⊗ D ⟶ D') (g : E ⟶ E') :
    (α_ C V W).inv ≫
      (((C ◁ a) ≫ (α_ C D E).inv ≫ (f ⊗ₘ g)) ▷ W) ≫
      ((D' ⊗ E') ◁ b) ≫ tensorμ D' E' F G =
    (C ◁ (a ⊗ₘ b)) ≫ (C ◁ tensorμ D E F G) ≫
      (α_ C (D ⊗ F) (E ⊗ G)).inv ≫
      (((α_ C D F).inv ≫ (f ▷ F)) ⊗ₘ (g ▷ G)) := by
  rw [← whisker_exchange_assoc, ← associator_inv_naturality_right_assoc]
  simp only [comp_whiskerRight, Category.assoc]
  rw [← associator_inv_naturality_middle_assoc]
  rw [← comp_whiskerRight_assoc]
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorCoefficientSeparation f g]
  rw [← whiskerLeft_comp_assoc, ← tensorHom_def']

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
