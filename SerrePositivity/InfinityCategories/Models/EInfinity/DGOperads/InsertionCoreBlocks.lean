module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.InsertionCore
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.InsertionPrefixNaturality

/-!
模型。文献の定義との比較は後で
# 三ブロックの連結上でのテンソル代入

概要：Berger–Moerdijk §1 の部分合成の入力代入を、明示的な三つのテンソル冪上で計算する。
方針：連結と分離を相殺し、前方の入力を越える係数の移動の自然性を使う。
規約：三つの区間の長さはそれぞれ零でもよい。
使われ方：代数で反復合成を評価する帰納段階で、最後の内側作用を取り出す。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers

variable {A : Type u} [CommRing A]

attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct
attribute [local implicit_reducible] _root_.SerrePositivity.TensorPowers.power

/-- 概要：三ブロックを連結した入力への代入は中間ブロックだけへの作用で計算できる（Berger–Moerdijk §1）。
方針：外側の連結を分離と相殺し、中間と後方の連結を係数移動の自然性で相殺する。
規約：係数と前方ブロックの交換には Koszul 対称性が含まれる。
使われ方：反復全合成の評価を、最後の演算の作用と残りの評価へ分解する。 -/
lemma tensorInsertionCore_on_blocks (X C : Complex A) (s n t : ℕ)
    (θ : C ⊗ power X n ⟶ X) :
    (C ◁ ((power X s ◁ (appendIso X n t).hom) ≫ (appendIso X s (n + t)).hom)) ≫
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionCore X C s n t θ =
    (α_ C (power X s) (power X n ⊗ power X t)).inv ≫
      ((β_ C (power X s)).hom ▷ (power X n ⊗ power X t)) ≫
      (α_ (power X s) C (power X n ⊗ power X t)).hom ≫
      (power X s ◁ (α_ C (power X n) (power X t)).inv) ≫
      (power X s ◁ (θ ▷ power X t)) ≫ (appendIso X s (t + 1)).hom := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionCore
  simp only [whiskerLeft_comp, Category.assoc, whiskerLeft_hom_inv_assoc]
  rw [reassoc_of% (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.insertionPrefix_naturality C (power X s) (appendIso X n t).hom)]
  rw [← whiskerLeft_comp_assoc (power X s)]
  simp only [whiskerLeft_hom_inv, whiskerLeft_id, Category.id_comp]

/-- 概要：位置 s への標準の代入を三ブロックの連結上で計算する（Berger–Moerdijk §1）。
方針：標準の代入を区間長を明示した代入へ移し、入力の arity の移送を相殺する。
規約：外側の残りの入力数は s+t、指定位置は s。
使われ方：代数の部分合成公理をブロックごとの評価へ接続する。 -/
lemma tensorInsertionAction_on_blocks (X C : Complex A) (s n t : ℕ)
    (θ : C ⊗ power X n ⟶ X) :
    (C ◁ ((power X s ◁ (appendIso X n t).hom) ≫
      (appendIso X s (n + t)).hom ≫
      eqToHom (congrArg (power X) (by omega : s + (n + t) = s + t + n)))) ≫
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionAction X C (s + t) n ⟨s, by omega⟩ θ =
    (α_ C (power X s) (power X n ⊗ power X t)).inv ≫
      ((β_ C (power X s)).hom ▷ (power X n ⊗ power X t)) ≫
      (α_ (power X s) C (power X n ⊗ power X t)).hom ≫
      (power X s ◁ (α_ C (power X n) (power X t)).inv) ≫
      (power X s ◁ (θ ▷ power X t)) ≫ (appendIso X s (t + 1)).hom ≫
      eqToHom (congrArg (power X) (by omega : s + (t + 1) = s + t + 1)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionAction_at_sum]
  simp only [whiskerLeft_comp, Category.assoc]
  simp only [← whiskerLeft_comp_assoc, eqToHom_trans, eqToHom_refl, whiskerLeft_id,
    Category.id_comp]
  erw [reassoc_of% (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionCore_on_blocks X C s n t θ)]
  simp only [whiskerLeft_comp, Category.assoc]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
