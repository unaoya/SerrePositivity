module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorFamilyLastSwap

/-!
模型。文献の定義との比較は後で
# 末尾交換後の分離と尾への制限

概要：Berger–Moerdijk §1 の末尾二入力の交換を、分離同型の尾への制限と比較する。
方針：交換後の族を先頭と尾で記述し、結合子の移送で正規化する。
規約：前半の入力を保ち、末尾の二因子だけを交換する。
使われ方：末尾交換と分離の可換性の帰納法の一段を与える。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.Coxeter

variable {A : Type u} [CommRing A]

attribute [local implicit_reducible] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyLastSwapTail
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct
attribute [local irreducible] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLastTwo CategoryTheory.eqToHom

/-- 概要：末尾交換後の前半の有限テンソルは元の前半と等しい（Berger–Moerdijk §1）。
方針：最後の隣接互換が前半の添字を固定することを使う。
規約：前半の長さは n。
使われ方：分離同型の結合子の中央の対象を正規化する。 -/
lemma tensorFamily_lastSwap_prefix_obj (n : ℕ) (V : Fin (n + 2) → Complex A) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun i => V (adjacentTransposition (Fin.last n) i.castSucc.castSucc)) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun i => V i.castSucc.castSucc) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.adjacentLast_prefix]

/-- 概要：末尾交換後の二因子の対は元の末尾二因子を逆順にした対象に等しい（Berger–Moerdijk §1）。
方針：最後の隣接互換を末尾二位置で評価する。
規約：対は右括弧の内部のテンソル積。
使われ方：分離同型の結合子の右の対象を正規化する。 -/
lemma tensorFamily_lastSwap_pair_obj (n : ℕ) (V : Fin (n + 2) → Complex A) :
    V (adjacentTransposition (Fin.last n) (Fin.last n).castSucc) ⊗
        V (adjacentTransposition (Fin.last n) (Fin.last (n + 1))) =
      V (Fin.last (n + 1)) ⊗ V (Fin.last n).castSucc := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.adjacentLast_penultimate, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.adjacentLast_last]

/-- 概要：先頭と尾で記述した末尾交換後の分離は尾の分離を正規化した射に一致する（Berger–Moerdijk §1）。
方針：分離の再帰式を使い、前半と末尾の対の移送を逆結合子に通す。
規約：終域は元の前半と交換した末尾の対に同定する。
使われ方：末尾交換と分離の可換性の帰納法で帰納仮定を適用する。 -/
lemma tensorFamilySplitLastTwo_lastSwap_tail_rec (n : ℕ)
    (V : Fin (n + 3) → Complex A) :
    eqToHom (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyLastSwapTail_source_obj n V).symm ≫
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLastTwo (n + 1) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyLastSwapTail n V)).hom ≫
        eqToHom (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyLastSwapTail_output_obj n V) =
      (V 0 ◁ ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLastTwo n
        (fun i => V (adjacentTransposition (Fin.last n) i).succ)).hom ≫
          eqToHom (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily_lastSwap_output_obj n (fun i => V i.succ)))) ≫
        (α_ (V 0) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun i => V i.castSucc.castSucc.succ))
          (V (Fin.last (n + 2)) ⊗ V (Fin.last (n + 1)).castSucc)).inv := by
  have hrec := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLastTwo_succ n (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyLastSwapTail n V)
  conv_lhs =>
    arg 2
    arg 1
    rw [hrec]
  simp only [eqToHom_refl, Category.id_comp]
  have h := @_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.associator_inv_eqToHom_pair (Complex A) (by infer_instance) (by infer_instance)
    (V 0) _ _ _ _
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily_lastSwap_prefix_obj n (fun i => V i.succ))
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily_lastSwap_pair_obj n (fun i => V i.succ))
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyLastSwapTail, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily, Fin.castSucc_succ,
    Fin.castSucc_zero, Fin.cases_zero, Fin.cases_succ] at h ⊢
  dsimp only [Fin.cases, Fin.induction, Fin.induction.go, Fin.last,
    Fin.castSucc, Fin.castAdd, Fin.castLE, Fin.succ] at h ⊢
  simp only [Category.assoc]
  conv_lhs =>
    arg 2
    rw [← h]
  simp only [whiskerLeft_comp, Category.assoc]

/-- 概要：元の末尾交換後の分離を尾の分離へ帰着する（Berger–Moerdijk §1）。
方針：交換後の族の比較と先頭を分ける再帰式を合成する。
規約：始域は先頭と交換後の尾、終域は元の前半と交換した末尾の対。
使われ方：末尾交換と分離の可換性の帰納法で直接用いる。 -/
lemma tensorFamilySplitLastTwo_lastSwap_succ (n : ℕ)
    (V : Fin (n + 3) → Complex A) :
    eqToHom (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily_adjacentSucc_obj (n + 1) V (Fin.last n)).symm ≫
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLastTwo (n + 1)
          (fun i => V (adjacentTransposition (Fin.last (n + 1)) i))).hom ≫
        eqToHom (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily_lastSwap_output_obj (n + 1) V) =
      (V 0 ◁ ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLastTwo n
        (fun i => V (adjacentTransposition (Fin.last n) i).succ)).hom ≫
          eqToHom (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily_lastSwap_output_obj n (fun i => V i.succ)))) ≫
        (α_ (V 0) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun i => V i.castSucc.castSucc.succ))
          (V (Fin.last (n + 2)) ⊗ V (Fin.last (n + 1)).castSucc)).inv := by
  exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLastTwo_lastSwap_succ_compare n V).trans
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLastTwo_lastSwap_tail_rec n V)

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
