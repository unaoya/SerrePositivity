module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.Tactic.CategoryTheory.Monoidal.Basic

/-!
模型。文献の定義との比較は後で
# 単位係数を代入する反復合成の構造射

概要：Berger–Moerdijk §1 の全合成の右単位則で、最後の単位係数の代入を縮約する。
方針：係数射と単位の縮約の自然性、単位との交換、結合子の整合性を使う。
規約：残る入力族 U は任意の対象でよい。
使われ方：全ての単位演算を代入する反復合成の帰納段階を処理する。
-/

@[expose] public section

universe v u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- 概要：最後の単位係数の代入と残りの単位族の縮約は一つの右単位子にまとめられる（Berger–Moerdijk §1）。
方針：係数射を後へ移し、単位との交換を単位子で表して整合性を用いる。
規約：c は残る単位族の縮約、e は係数の arity の移送を表す。
使われ方：反復合成の右単位則の帰納段階で構造射を整理する。 -/
lemma tensorSubstitution_rightUnit {R R' U : C} (c : U ⟶ 𝟙_ C) (e : R ⟶ R') :
    (R ◁ (β_ U (𝟙_ C)).hom) ≫ (α_ R (𝟙_ C) U).inv ≫
      (((ρ_ R).hom ≫ e) ▷ U) ≫ (R' ◁ c) ≫ (ρ_ R').hom =
    (R ◁ ((c ▷ 𝟙_ C) ≫ (ρ_ (𝟙_ C)).hom)) ≫ (ρ_ R).hom ≫ e := by
  simp only [comp_whiskerRight, Category.assoc]
  rw [← whisker_exchange_assoc e c, rightUnitor_naturality]
  rw [braiding_tensorUnit_right]
  simp only [whiskerLeft_comp, Category.assoc]
  monoidal

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
