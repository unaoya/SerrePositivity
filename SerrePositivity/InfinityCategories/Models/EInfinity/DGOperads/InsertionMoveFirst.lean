module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.MoveFirstInputTensor
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.InsertionPrefixNaturality
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.InsertionZero
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.InsertionCore

/-!
模型。文献の定義との比較は後で
# 標準の入力代入射の先頭から指定位置への移動

概要：Berger–Moerdijk §1 の入力代入射で、先頭の演算を指定した位置へ動かす。
方針：三ブロックの連結を前置し、入力ブロックの回転と演算の自然性を使う。
規約：指定位置は a、全体の外側入力数は a+b+1。
使われ方：Schur 作用の先頭の部分合成則を任意位置へ拡張する。
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

/-- 概要：入力ブロックを回転して位置 a に代入する計算は、先頭で代入して出力を回転する計算に等しい（Berger–Moerdijk §1）。
方針：三ブロックの連結同型で比較し、回転と演算の適用の自然性を使う。
規約：arity n は零を許し、後半 b 入力を固定する。
使われ方：標準の入力代入射を先頭の代数公理の入力射へ帰着する。 -/
lemma tensorInsertionAction_moveFirst (X C : Complex A) (a b n : ℕ)
    (θ : C ⊗ power X n ⟶ X) :
    (C ◁ (permutationAction X (a + b + n) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadMoveFirstBlock a b n)).asIso.hom) ≫
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionAction X C (a + b) n ⟨a, by omega⟩ θ =
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionAction X C (a + b) n 0 θ ≫
      (permutationAction X (a + b + 1) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadMoveFirstBlock a b 1)).asIso.hom := by
  let J := (power X n ◁ (appendIso X a b).hom) ≫ (appendIso X n (a + b)).hom ≫
    eqToHom (congrArg (power X) (by omega : n + (a + b) = a + b + n))
  have : IsIso J := by dsimp [J]; infer_instance
  apply (cancel_epi (C ◁ J)).1
  rw [← whiskerLeft_comp_assoc]
  dsimp only [J]
  simp only [Category.assoc]
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.appendIso_moveFirstBlock, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionAction_zero]
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionAction_at_sum]
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionCore
  simp only [whiskerLeft_comp, Category.assoc]
  simp only [whiskerLeft_eqToHom, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
    whiskerLeft_hom_inv_assoc]
  simp only [Category.comp_id]
  rw [reassoc_of% (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.insertionPrefix_naturality C (power X a) (appendIso X n b).hom)]
  rw [← whiskerLeft_comp_assoc (power X a)]
  simp only [whiskerLeft_hom_inv, whiskerLeft_id, Category.id_comp]
  rw [← whiskerLeft_comp_assoc C, ← whiskerLeft_comp_assoc C]
  simp only [Category.assoc]
  erw [← reassoc_of% (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.insertionRotation_naturality (W := power X a) (T := power X b) θ)]
  rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc]
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.appendIso_moveFirstInput]
  simp only [eqToHom_refl, Category.comp_id]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
