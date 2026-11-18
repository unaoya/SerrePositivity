module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorSubstitutionNested
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorSubstitutionTransport

/-!
模型。文献の定義との比較は後で
# 平行な代入の後の先頭ブロックの合成

概要：Berger–Moerdijk §1 の平行な交換と入れ子の結合を四因子の代入へまとめる。
方針：後半の代入を先に行い、先頭の二因子を一つの演算へ合成する。
規約：元の入力順序は係数 R、先頭演算 S、内側の族 V、後半の族 L。
使われ方：先頭への部分合成と全入力への代入の両立を証明する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded

/-- 概要：平行な交換と先頭の入れ子の結合を一つの代入則へまとめる（Berger–Moerdijk §1）。
方針：係数射を代入の内部へ移し、仮定の二つの結合則を適用する。
規約：L を先に代入し、その後 S と V の合成結果を代入する。
使われ方：全合成の二ブロック分解に平行則と入れ子則を同時に適用する。 -/
lemma tensorSubstitutionStep_first_nested {A : Type u} [CommRing A]
    {R S V L T R₁ T₁ S₁ O : Complex A}
    (f : R ⊗ S ⟶ T) (g : T ⊗ L ⟶ T₁) (a : R ⊗ L ⟶ R₁)
    (b : R₁ ⊗ S ⟶ T₁) (h : T₁ ⊗ V ⟶ O) (w : S ⊗ V ⟶ S₁)
    (q : R₁ ⊗ S₁ ⟶ O)
    (hf : (f ▷ L) ≫ g = (α_ R S L).hom ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep a b)
    (hv : (b ▷ V) ≫ h = (α_ R₁ S V).hom ≫ (R₁ ◁ w) ≫ q) :
    (f ▷ (V ⊗ L)) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep g h =
      (α_ R S (V ⊗ L)).hom ≫ (R ◁ (α_ S V L).inv) ≫
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep a ((R₁ ◁ w) ≫ q) := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep_first_pre, hf]
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep, comp_whiskerRight, Category.assoc]
  rw [hv]
  rw [associator_naturality_left_assoc]
  rw [CategoryTheory.BraidedCategory.braiding_tensor_left_hom]
  simp only [whiskerLeft_comp, Category.assoc]
  monoidal

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
