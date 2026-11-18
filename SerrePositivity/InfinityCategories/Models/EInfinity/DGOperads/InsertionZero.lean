module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Insertion
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.FirstSlotPowerComparison
public import Mathlib.Tactic.CategoryTheory.Monoidal.Basic

/-!
模型。文献の定義との比較は後で
# 標準のテンソル代入射の先頭位置

概要：Berger–Moerdijk §1 の代数の部分合成則で、先頭への代入射を標準の連結の逆射で表す。
方針：挿入位置より前の空の入力族に付く単位因子を相殺する。
規約：入力数を m+n から n+m へ移送して前半 n 入力へ演算を適用する。
使われ方：有限族から構成した先頭の入力射を既存の tensorInsertionAction と同定する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers

/-- 概要：先頭より前の単位入力族の移動は何も変えない（Berger–Moerdijk §1）。
方針：単位対象との交換を単位子で表し、モノイダル整合性と左単位子の自然性を使う。
規約：係数 C と残りの入力 T の順序を保つ。
使われ方：先頭へのテンソル代入から空の前半を除く。 -/
lemma tensorInsertion_unitPrefix {C₀ : Type u} [Category.{v} C₀]
    [MonoidalCategory C₀] [SymmetricCategory C₀] {C T Y : C₀} (b : C ⊗ T ⟶ Y) :
    (C ◁ (λ_ T).inv) ≫ (α_ C (𝟙_ C₀) T).inv ≫
      ((β_ C (𝟙_ C₀)).hom ▷ T) ≫ (α_ (𝟙_ C₀) C T).hom ≫
      ((𝟙_ C₀) ◁ b) ≫ (λ_ Y).hom = b := by
  have h : (C ◁ (λ_ T).inv) ≫ (α_ C (𝟙_ C₀) T).inv ≫
      ((β_ C (𝟙_ C₀)).hom ▷ T) ≫ (α_ (𝟙_ C₀) C T).hom = (λ_ (C ⊗ T)).inv := by
    rw [braiding_tensorUnit_right]
    simp only [comp_whiskerRight, Category.assoc]
    monoidal
  rw [reassoc_of% h, ← leftUnitor_inv_naturality_assoc, Iso.inv_hom_id, Category.comp_id]

variable {A : Type u} [CommRing A]

attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct

/-- 概要：標準の先頭への代入射は前半 n 入力への演算の適用である（Berger–Moerdijk §1）。
方針：代入射の定義で先頭位置を指定し、零乗の連結と単位入力族の移動を相殺する。
規約：最初に入力数 m+n を n+m へ移す。
使われ方：補助入力射との比較を通して Schur 作用の標準の代数公理を得る。 -/
lemma tensorInsertionAction_zero (X C : Complex A) (m n : ℕ) (θ : C ⊗ power X n ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionAction X C m n 0 θ =
      (C ◁ eqToHom (congrArg (power X) (Nat.add_comm m n))) ≫
      (C ◁ (appendIso X n m).inv) ≫ (α_ C (power X n) (power X m)).inv ≫
      (θ ▷ power X m) := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionAction
  dsimp only [Fin.val_zero, Nat.sub_zero]
  simp only [appendIso, Iso.trans_hom, Iso.trans_inv, eqToIso.hom, eqToIso.inv,
    Category.assoc, eqToHom_trans]
  simp only [whiskerLeft_comp, Category.assoc, eqToHom_trans_assoc,
    eqToHom_refl, Category.comp_id]
  erw [← whiskerLeft_comp_assoc (𝟙_ (Complex A)),
    ← whiskerLeft_comp_assoc (𝟙_ (Complex A))]
  erw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertion_unitPrefix]
  simp only [Category.assoc]

/-- 概要：既存の先頭への代入射は補助入力射の入力と出力を移送したものに等しい（Berger–Moerdijk §1）。
方針：両方の射を標準の分離と演算の適用の式へ移して比較する。
規約：入力を m+n から n+m、出力を 1+m から m+1 へ移す。
使われ方：一般の Schur 入力で証明した先頭の結合則を既存の代数公理へ戻す。 -/
lemma tensorInsertionAction_zero_eq_firstSlot (X C : Complex A) (m n : ℕ)
    (θ : C ⊗ power X n ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionAction X C m n 0 θ =
      (C ◁ eqToHom (congrArg (power X) (Nat.add_comm m n))) ≫
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.firstSlotPowerAction X C n m θ ≫
      eqToHom (congrArg (power X) (Nat.one_add m)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.firstSlotPowerAction_normalized, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionAction_zero]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
