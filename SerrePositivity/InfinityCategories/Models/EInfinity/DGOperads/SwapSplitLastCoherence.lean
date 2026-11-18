module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.SplitPairCoherence

/-!
模型。文献の定義との比較は後で
# 先頭二因子の交換と最後の因子の分離

概要：Berger–Moerdijk §1 の隣接交換の帰納法で、先頭二因子の交換と末尾の分離を比較する。
方針：結合子の整合性と交換射に対する結合子の自然性を使う。
規約：先頭二因子 R,S のみを交換し、残りの L,V の順序を保つ。
使われ方：末尾を固定する隣接交換と最後の因子の分離の可換性の基底に用いる。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- 概要：先頭二因子の交換は四因子の最後の因子の分離と両立する（Berger–Moerdijk §1）。
方針：結合子の二つの整合性の式と交換射についての自然性を組み合わせる。
規約：右括弧の R,S,L,V から、先頭二因子を交換して末尾 V を分離する。
使われ方：有限テンソル族の先頭交換と最後の分離を比較する。 -/
lemma frontSwap_splitLast_coherence (R S L V : C) :
    (α_ R S (L ⊗ V)).inv ≫ ((β_ R S).hom ▷ (L ⊗ V)) ≫
        (α_ S R (L ⊗ V)).hom ≫ (S ◁ (α_ R L V).inv) ≫ (α_ S (R ⊗ L) V).inv =
      (R ◁ (α_ S L V).inv) ≫ (α_ R (S ⊗ L) V).inv ≫
        (((α_ R S L).inv ≫ ((β_ R S).hom ▷ L) ≫ (α_ S R L).hom) ▷ V) := by
  have h₁ : (R ◁ (α_ S L V).inv) ≫ (α_ R (S ⊗ L) V).inv ≫
      ((α_ R S L).inv ▷ V) =
      (α_ R S (L ⊗ V)).inv ≫ (α_ (R ⊗ S) L V).inv := by monoidal
  have h₂ : (α_ S R (L ⊗ V)).hom ≫ (S ◁ (α_ R L V).inv) ≫
      (α_ S (R ⊗ L) V).inv =
      (α_ (S ⊗ R) L V).inv ≫ ((α_ S R L).hom ▷ V) := by monoidal
  simp only [comp_whiskerRight]
  rw [h₂, associator_inv_naturality_left_assoc]
  simpa only [Category.assoc] using congrArg
    (fun f => f ≫ (((β_ R S).hom ▷ L) ▷ V) ≫ ((α_ S R L).hom ▷ V)) h₁.symm

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
