module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorSubstitutionNaturality
public import Mathlib.Tactic.CategoryTheory.Monoidal.Basic

/-!
模型。文献の定義との比較は後で
# 二段のテンソル代入の結合

概要：Berger–Moerdijk §1 の二段の反復代入を、最後の二因子をまとめた代入と比較する。
方針：braiding の自然性と hexagon、結合子の pentagon で因子の移動を整理する。
規約：最後の因子を先に代入する順序を保ち、残りの因子の順序を変えない。
使われ方：全入力への反復合成の末尾二入力を二位置への合成射へまとめる。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.BraidedCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- 概要：三因子を右から移動する交換は最後の二因子をまとめた交換と一致する（Berger–Moerdijk §1）。
方針：braiding の自然性で先頭の交換を移し、左右の hexagon を使う。
規約：全ての braiding は正の向きに適用する。
使われ方：二段のテンソル代入の三因子の移動を比較する。 -/
@[reassoc]
lemma substitutionBraiding_three (V U L : C) :
    (β_ (V ⊗ U) L).hom ≫ (L ◁ (β_ V U).hom) =
      (α_ V U L).hom ≫ (β_ V (U ⊗ L)).hom ≫
        ((β_ U L).hom ▷ V) ≫ (α_ L U V).hom := by
  rw [← braiding_naturality_left, braiding_tensor_left_hom, braiding_tensor_right_hom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

omit [BraidedCategory C] in
/-- 概要：四因子の右から左への括弧の移動を比較する（Berger–Moerdijk §1）。
方針：結合子の pentagon による整合性を使う。
規約：最終的には全て左括弧へ移す。
使われ方：二段のテンソル代入で係数を含む結合子を整理する。 -/
@[reassoc]
lemma substitutionAssociator_four (R L U V : C) :
    (α_ R (L ⊗ U) V).inv ≫ ((α_ R L U).inv ▷ V) =
      (R ◁ (α_ L U V).hom) ≫ (α_ R L (U ⊗ V)).inv ≫
        (α_ (R ⊗ L) U V).inv := by
  monoidal

/-- 概要：係数を含む四因子の二段の交換をまとめた交換と比較する（Berger–Moerdijk §1）。
方針：結合子の自然性で braiding を左 whisker へ集め、三因子の交換則を使う。
規約：係数 R は移動せず、残りを L,U,V の順へ移す。
使われ方：二段のテンソル代入の結合則の構造射の部分を証明する。 -/
@[reassoc]
lemma substitutionBraiding_four (R V U L : C) :
    (R ◁ (β_ (V ⊗ U) L).hom) ≫ (α_ R L (V ⊗ U)).inv ≫
        ((R ⊗ L) ◁ (β_ V U).hom) ≫ (α_ (R ⊗ L) U V).inv =
      (R ◁ (α_ V U L).hom) ≫ (R ◁ (β_ V (U ⊗ L)).hom) ≫
        (α_ R (U ⊗ L) V).inv ≫ ((R ◁ (β_ U L).hom) ▷ V) ≫
        ((α_ R L U).inv ▷ V) := by
  rw [← associator_inv_naturality_right_assoc,
    ← associator_inv_naturality_middle_assoc, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.substitutionAssociator_four]
  simp only [← whiskerLeft_comp_assoc]
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.substitutionBraiding_three]

/-- 概要：二段のテンソル代入は最後の二因子をまとめた代入と一致する（Berger–Moerdijk §1）。
方針：部分合成の射を自然性で構造射の後へ移し、四因子の交換の比較を使う。
規約：最後の L、その前の U、残りの V の順に合成する。
使われ方：任意の長さの反復合成の末尾二入力をまとめる。 -/
@[reassoc]
lemma tensorSubstitutionStep_assoc {A : Type u} [CommRing A]
    {R V U L R₁ R₂ O : _root_.SerrePositivity.DifferentialGraded.Complex A}
    (f : R ⊗ L ⟶ R₁) (g : R₁ ⊗ U ⟶ R₂) (h : R₂ ⊗ V ⟶ O) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep f (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep g h) =
      (R ◁ (α_ V U L).hom) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep f g) h := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep, comp_whiskerRight, Category.assoc]
  rw [← whisker_exchange_assoc f (β_ V U).hom,
    associator_inv_naturality_left_assoc f U V, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.substitutionBraiding_four_assoc]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
