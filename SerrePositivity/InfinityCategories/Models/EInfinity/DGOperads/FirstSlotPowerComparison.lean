module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.FirstSlotPowerAction
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorFamilyPowerSplitAppend

/-!
模型。文献の定義との比較は後で
# 有限族から得た先頭入力射の標準の連結による式

概要：Berger–Moerdijk §1 の先頭への入力作用を既存のテンソル冪の連結同型で表す。
方針：有限族由来の分離を appendIso の逆同型へ置き換え、先頭の単位因子を相殺する。
規約：出力の入力数を 1+m から m+1 へ移す。
使われ方：補助入力射を標準の tensorInsertionAction の先頭位置へ同定する。
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

attribute [local implicit_reducible] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct

/-- 概要：先頭の再結合は一次と後半への分離の逆射で表せる（Berger–Moerdijk §1）。
方針：一定族の同一視を展開し、単位子の逆射を尾の同一視へ通す。
規約：一次のテンソル冪に含まれる単位因子を補う。
使われ方：先頭の再結合を標準の連結同型へ移す。 -/
lemma tensorFamilyHeadAssemblyToPower_split (X : Complex A) (m : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyHeadAssemblyToPower X m =
      ((ρ_ X).inv ▷ power X m) ≫ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyPowerSplitIso X 1 m).inv := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyHeadAssemblyToPower _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyHeadAssembly _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyPowerSplitIso
  simp only [Iso.trans_inv, Iso.symm_inv, eqToIso.inv, eqToIso.hom, tensorIso_inv,
    eqToHom_refl, id_tensorHom, Category.assoc]
  rw [whisker_exchange_assoc]
  rfl

/-- 概要：先頭の再結合は右単位因子を補って標準の連結を行う射である（Berger–Moerdijk §1）。
方針：有限族由来の分離と標準の連結の比較を使う。
規約：出力の長さは 1+m。
使われ方：既存の先頭入力へのテンソル代入と比較する。 -/
lemma tensorFamilyHeadAssemblyToPower_append (X : Complex A) (m : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyHeadAssemblyToPower X m =
      ((ρ_ X).inv ▷ power X m) ≫ (appendIso X 1 m).hom := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyHeadAssemblyToPower_split, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyPowerSplitIso_eq_append]
  rfl

/-- 概要：先頭の再結合は m+1 入力への移送後に恒等射となる（Berger–Moerdijk §1）。
方針：一次の標準連結の式を使い、右単位子と arity の移送を相殺する。
規約：始域 X⊗power X m を power X (m+1) と同一視する。
使われ方：標準の先頭への代入の出力の括弧付けへ移す。 -/
lemma tensorFamilyHeadAssemblyToPower_normalized (X : Complex A) (m : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyHeadAssemblyToPower X m ≫
      eqToHom (congrArg (power X) (Nat.one_add m)) = 𝟙 (power X (m + 1)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyHeadAssemblyToPower_append, appendIso_one_left]
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id,
    ← comp_whiskerRight, Iso.inv_hom_id, id_whiskerRight]
  rfl

/-- 概要：補助的な先頭入力射は標準の分離と指定した演算の適用で計算できる（Berger–Moerdijk §1）。
方針：分離を標準連結の逆射へ移し、最後の再結合を出力の arity の移送で相殺する。
規約：入力を n+m、出力を m+1 と表す。
使われ方：tensorInsertionAction の先頭位置の式へ接続する。 -/
lemma firstSlotPowerAction_normalized (X C : Complex A) (n m : ℕ) (θ : C ⊗ power X n ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.firstSlotPowerAction X C n m θ ≫ eqToHom (congrArg (power X) (Nat.one_add m)) =
      (C ◁ (appendIso X n m).inv) ≫ (α_ C (power X n) (power X m)).inv ≫
        (θ ▷ power X m) := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.firstSlotPowerAction
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyPowerSplitIso_eq_append]
  simp only [Iso.symm_hom, Category.assoc]
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyHeadAssemblyToPower_normalized]
  erw [Category.comp_id]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
