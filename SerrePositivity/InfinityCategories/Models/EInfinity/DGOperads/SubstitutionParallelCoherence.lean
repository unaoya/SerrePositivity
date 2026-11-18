module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorSubstitutionAssociativity

/-!
模型。文献の定義との比較は後で
# 異なる入力への代入を交換する構造射

概要：Berger–Moerdijk §1 の異なる入力への代入の交換を有限族へ持ち上げる構造射を比較する。
方針：braiding の自然性と hexagon により三因子の交換をまとめ、結合子を整理する。
規約：外側の係数 R は交換せず、U を V と L のブロックの後へ移す。
使われ方：二段の平行なテンソル代入の比較を証明する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.BraidedCategory

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- 概要：二段の入力交換の構造射は一つの入力ブロックをまとめて交換したものに一致する（Berger–Moerdijk §1）。
方針：U と L⊗V の braiding を展開し、V と L の交換に関する自然性を適用する。
規約：最終的な入力順序は R,L,V,U。
使われ方：異なる入力への二つの代入の結合則を有限族へ接続する。 -/
@[reassoc]
lemma substitutionParallel_four (R U V L : C) :
    ((R ⊗ U) ◁ (β_ V L).hom) ≫ (α_ (R ⊗ U) L V).inv ≫
      ((α_ R U L).hom ▷ V) ≫ ((R ◁ (β_ U L).hom) ▷ V) ≫
      ((α_ R L U).inv ▷ V) ≫ (α_ (R ⊗ L) U V).hom ≫
      ((R ⊗ L) ◁ (β_ U V).hom) ≫ (α_ (R ⊗ L) V U).inv =
    (α_ R U (V ⊗ L)).hom ≫ (R ◁ (β_ U (V ⊗ L)).hom) ≫
      (α_ R (V ⊗ L) U).inv ≫ ((R ◁ (β_ V L).hom) ▷ U) ≫
      ((α_ R L V).inv ▷ U) := by
  calc
    _ = (α_ R U (V ⊗ L)).hom ≫
        (R ◁ ((U ◁ (β_ V L).hom) ≫ (β_ U (L ⊗ V)).hom)) ≫
        (α_ R (L ⊗ V) U).inv ≫ ((α_ R L V).inv ▷ U) := by
      rw [braiding_tensor_right_hom]
      simp only [whiskerLeft_comp, Category.assoc]
      monoidal
    _ = (α_ R U (V ⊗ L)).hom ≫
        (R ◁ ((β_ U (V ⊗ L)).hom ≫ ((β_ V L).hom ▷ U))) ≫
        (α_ R (L ⊗ V) U).inv ≫ ((α_ R L V).inv ▷ U) := by
      rw [braiding_naturality_right]
    _ = _ := by
      simp only [whiskerLeft_comp, Category.assoc]
      monoidal

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
