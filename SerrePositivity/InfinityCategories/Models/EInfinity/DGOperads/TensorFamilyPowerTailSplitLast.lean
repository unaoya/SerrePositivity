module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorFamilyPowerSplitLast

/-!
模型。文献の定義との比較は後で
# 末尾入力を含む有限族の連結の最後の分離

概要：Berger–Moerdijk §1 の反復合成で、最後の演算の入力を未処理の末尾へまとめる。
方針：有限族の最後の分離の式に末尾をテンソルし、連結の結合則を使う。
規約：最後の演算の入力、元の末尾入力の順序を保つ。
使われ方：末尾入力を残した反復合成のテンソル射の再帰の入力側を計算する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers
open scoped _root_.BigOperators

variable {A : Type u} [CommRing A]

attribute [local implicit_reducible] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily _root_.SerrePositivity.TensorPowers.power
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct

/-- 概要：最後の入力と末尾を先に連結してから前半の全入力を連結できる（Berger–Moerdijk §1）。
方針：有限族の最後の分離、連結の添字の自然性、三ブロックの結合則を用いる。
規約：出力は元の有限族の総 arity と末尾入力数の和で表す。
使われ方：最後の演算の入力を新しい末尾にまとめる再帰式に用いる。 -/
lemma tensorPowerFamilyTail_splitLast_inv (K : Complex A) (n k : ℕ)
    (s : Fin (n + 1) → ℕ) :
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast n (fun j => power K (s j))).inv ▷ power K k) ≫
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso K (n + 1) s).hom ▷ power K k) ≫
      (appendIso K (∑ j, s j) k).hom =
    (α_ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun j => power K (s j.castSucc)))
      (power K (s (Fin.last n))) (power K k)).hom ≫
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso K n (fun j => s j.castSucc)).hom ⊗ₘ
        (appendIso K (s (Fin.last n)) k).hom) ≫
      (appendIso K (∑ j : Fin n, s j.castSucc) (s (Fin.last n) + k)).hom ≫
      eqToHom (congrArg (power K) (by
        rw [Fin.sum_univ_castSucc]
        omega : (∑ j : Fin n, s j.castSucc) + (s (Fin.last n) + k) = (∑ j, s j) + k)) := by
  rw [← comp_whiskerRight_assoc, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso_splitLast_inv]
  simp only [comp_whiskerRight, Category.assoc, tensorHom_id]
  rw [appendIso_index_left K (Fin.sum_univ_castSucc s).symm k]
  rw [tensorHom_def]
  simp only [Category.assoc]
  rw [← associator_naturality_left_assoc]
  have h := congrArg (fun z => z ≫ eqToHom (congrArg (power K) (by
    rw [Fin.sum_univ_castSucc]
    omega : (∑ j : Fin n, s j.castSucc) + (s (Fin.last n) + k) = (∑ j, s j) + k)))
    (appendIso_associativity K (∑ j : Fin n, s j.castSucc) (s (Fin.last n)) k)
  simp only [Category.assoc, eqToHom_trans] at h
  rw [h]

/-- 概要：最後と末尾の入力の合計を任意の等しい長さで表せる（Berger–Moerdijk §1）。
方針：新しい末尾の長さの等式を消去し、末尾付きの最後の分離の式を使う。
規約：長さの表示の移送は入力の順序を変えない。
使われ方：係数の再帰が要求する k+l の末尾長へ、実際の l+k 入力を移す。 -/
lemma tensorPowerFamilyTail_splitLast_inv_cast (K : Complex A) (n k : ℕ)
    (s : Fin (n + 1) → ℕ) {r : ℕ} (hr : s (Fin.last n) + k = r) :
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast n (fun j => power K (s j))).inv ▷ power K k) ≫
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso K (n + 1) s).hom ▷ power K k) ≫
      (appendIso K (∑ j, s j) k).hom =
    (α_ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun j => power K (s j.castSucc)))
      (power K (s (Fin.last n))) (power K k)).hom ≫
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso K n (fun j => s j.castSucc)).hom ⊗ₘ
        ((appendIso K (s (Fin.last n)) k).hom ≫ eqToHom (congrArg (power K) hr))) ≫
      (appendIso K (∑ j : Fin n, s j.castSucc) r).hom ≫
      eqToHom (congrArg (power K) (by
        rw [← hr, Fin.sum_univ_castSucc]
        omega : (∑ j : Fin n, s j.castSucc) + r = (∑ j, s j) + k)) := by
  subst r
  simpa only [eqToHom_refl, Category.comp_id] using _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyTail_splitLast_inv K n k s

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
