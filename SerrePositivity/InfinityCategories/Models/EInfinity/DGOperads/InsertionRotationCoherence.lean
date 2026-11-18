module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.Tactic.CategoryTheory.Monoidal.Basic

/-!
模型。文献の定義との比較は後で
# 演算の適用と先頭ブロックの回転

概要：Berger–Moerdijk §1 の入力代入射で、演算を適用してから先頭を動かす計算を比較する。
方針：係数と演算の入力を順に動かす式を六角形の式で一つのブロック交換へまとめる。
規約：末尾の入力族 T は動かさず、演算の出力を W の後へ置く。
使われ方：標準の入力代入射の挿入位置の移動則を証明する。
-/

@[expose] public section

universe v u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.BraidedCategory

variable {C₀ : Type u} [Category.{v} C₀] [MonoidalCategory C₀] [SymmetricCategory C₀]

/-- 概要：係数と入力をまとめたブロックの交換は入力と係数を順に交換する式に等しい（Berger–Moerdijk §1）。
方針：テンソル積に対する交換の六角形の式を展開し、結合子の整合性を使う。
規約：因子の順序を C,V,W,T から W,C,V,T へ変える。
使われ方：入力の先頭ブロックを動かす構造射を代入射の構造射へ同定する。 -/
@[reassoc]
lemma insertionRotation_coherence (C V W T : C₀) :
    (α_ C V (W ⊗ T)).inv ≫ (α_ (C ⊗ V) W T).inv ≫
      ((β_ (C ⊗ V) W).hom ▷ T) ≫ (α_ W (C ⊗ V) T).hom =
    (C ◁ ((α_ V W T).inv ≫ ((β_ V W).hom ▷ T) ≫ (α_ W V T).hom)) ≫
      (α_ C W (V ⊗ T)).inv ≫ ((β_ C W).hom ▷ (V ⊗ T)) ≫
      (α_ W C (V ⊗ T)).hom ≫ (W ◁ (α_ C V T).inv) := by
  rw [braiding_tensor_left_hom]
  simp only [comp_whiskerRight, whiskerLeft_comp, Category.assoc]
  monoidal

/-- 概要：演算を適用して出力を動かす計算は、入力ブロックを先に動かしてから演算を適用する式に等しい（Berger–Moerdijk §1）。
方針：演算の射を結合子と交換の自然性で後へ移し、回転の構造射の整合性を使う。
規約：θ は係数 C と入力 V から出力 X への任意の射。
使われ方：先頭への代入を指定位置への代入へ移す。 -/
lemma insertionRotation_naturality {C V W T X : C₀} (θ : C ⊗ V ⟶ X) :
    (α_ C V (W ⊗ T)).inv ≫ (θ ▷ (W ⊗ T)) ≫
      (α_ X W T).inv ≫ ((β_ X W).hom ▷ T) ≫ (α_ W X T).hom =
    (C ◁ ((α_ V W T).inv ≫ ((β_ V W).hom ▷ T) ≫ (α_ W V T).hom)) ≫
      (α_ C W (V ⊗ T)).inv ≫ ((β_ C W).hom ▷ (V ⊗ T)) ≫
      (α_ W C (V ⊗ T)).hom ≫ (W ◁ (α_ C V T).inv) ≫ (W ◁ (θ ▷ T)) := by
  rw [associator_inv_naturality_left_assoc]
  rw [← comp_whiskerRight_assoc, braiding_naturality_left]
  simp only [comp_whiskerRight, Category.assoc]
  rw [associator_naturality_middle, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.insertionRotation_coherence_assoc]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
