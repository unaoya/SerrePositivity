module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorFamilyFirstSwapSplitLast

/-!
模型。文献の定義との比較は後で
# 尾の前半の交換を持ち上げた入力族

概要：Berger–Moerdijk §1 の末尾を固定する隣接交換を先頭を固定した尾の交換として記述する。
方針：尾での隣接互換を Fin.cases で持ち上げ、最後の分離の始域と終域を同定する。
規約：先頭と最後の因子を固定する。
使われ方：任意の隣接位置と最後の分離の可換性の帰納段階を与える。
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

attribute [local implicit_reducible] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily Fin.cases Fin.induction Fin.induction.go
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct

/-- 概要：末尾を固定する隣接互換をずらすと、尾の値は元の隣接互換の値をずらしたものになる（Berger–Moerdijk §1）。
方針：ずらした置換の値と隣接互換の計算則を使う。
規約：添字の succ と castSucc の順序は可換なものとして比較する。
使われ方：尾の入力族の交換を全入力族の交換へ持ち上げる。 -/
lemma adjacentCastSucc_succ (n : ℕ) (i : Fin n) (j : Fin (n + 2)) :
    adjacentTransposition i.succ.castSucc j.succ =
      (adjacentTransposition i.castSucc j).succ := by
  have h := shiftPerm_succ (adjacentTransposition i.castSucc) j
  rw [shiftPerm_adjacent (n + 1) i.castSucc] at h
  exact h

/-- 概要：先頭を保ち、尾で末尾以外の隣接二因子を交換した入力族（Berger–Moerdijk §1）。
方針：Fin.cases の先頭に元の値、尾に持ち上げ前の交換後の値を置く。
規約：元の族の長さは n+3。
使われ方：交換後の最後の分離を先頭に関して再帰する。 -/
def tensorFamilyAdjacentCastTail (n : ℕ) (V : Fin (n + 3) → Complex A) (i : Fin n) :
    Fin (n + 3) → Complex A :=
  Fin.cases (V 0) (fun j => V (adjacentTransposition i.castSucc j).succ)

attribute [local implicit_reducible] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyAdjacentCastTail

/-- 概要：尾の交換を明示した入力族は全入力族の対応する隣接交換と一致する（Berger–Moerdijk §1）。
方針：先頭ではずらした置換の固定点の式、尾ではずらした値の計算を使う。
規約：全入力族では i.succ.castSucc の位置で交換する。
使われ方：等しい入力族の分離の比較へ適用する。 -/
lemma tensorFamilyAdjacentCastTail_eq (n : ℕ) (V : Fin (n + 3) → Complex A) (i : Fin n) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyAdjacentCastTail n V i =
      fun j => V (adjacentTransposition i.succ.castSucc j) := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · change V 0 = V (adjacentTransposition i.succ.castSucc 0)
    have h := shiftPerm_zero (adjacentTransposition i.castSucc)
    rw [shiftPerm_adjacent (n + 1) i.castSucc] at h
    exact congrArg V h.symm
  · change V (adjacentTransposition i.castSucc j).succ =
      V (adjacentTransposition i.succ.castSucc j.succ)
    exact congrArg V (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.adjacentCastSucc_succ n i j).symm

/-- 概要：尾の交換を明示した入力族のテンソル対象は先頭と交換後の尾のテンソルである（Berger–Moerdijk §1）。
方針：有限テンソルの一段の再帰と Fin.cases の計算則を使う。
規約：先頭の因子を左側に保つ。
使われ方：尾の交換の whisker の終域を分離の始域へ移す。 -/
lemma tensorFamilyAdjacentCastTail_source_obj (n : ℕ) (V : Fin (n + 3) → Complex A)
    (i : Fin n) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily (n + 3) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyAdjacentCastTail n V i) =
      V 0 ⊗ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily (n + 2) (fun j => V (adjacentTransposition i.castSucc j).succ) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyAdjacentCastTail, Fin.cases_zero, Fin.cases_succ]

/-- 概要：尾の交換を明示した族の最後の分離の終域を前半の交換と最後の因子で表す（Berger–Moerdijk §1）。
方針：先頭を展開し、持ち上げた隣接互換の前半と最後での値を計算する。
規約：前半を先頭と残りに分け、最後の因子を右側に保つ。
使われ方：尾の分離に帰納仮定を適用できる終域へ移す。 -/
lemma tensorFamilyAdjacentCastTail_output_obj (n : ℕ) (V : Fin (n + 3) → Complex A)
    (i : Fin n) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily (n + 2) (fun j => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyAdjacentCastTail n V i j.castSucc) ⊗
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyAdjacentCastTail n V i (Fin.last (n + 2)) =
      (V 0 ⊗ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily (n + 1) (fun j => V (adjacentTransposition i j).castSucc.succ)) ⊗
        V (Fin.last (n + 2)) := by
  change (V 0 ⊗ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily (n + 1)
      (fun j => V (adjacentTransposition i.castSucc j.castSucc).succ)) ⊗
      V (adjacentTransposition i.castSucc (Fin.last (n + 1))).succ = _
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.adjacentCastSucc_prefix, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.adjacentCastSucc_last]
  rfl

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
