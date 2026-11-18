module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorFamilySplitTwoRecursion

/-!
模型。文献の定義との比較は後で
# 末尾交換を先頭と尾で記述した入力族

概要：Berger–Moerdijk §1 の外側等変性で用いる末尾交換を先頭と尾に分解する。
方針：先頭を固定し、尾で最後の隣接互換を適用した族を明示する。
規約：末尾二因子以外の入力の順序は保つ。
使われ方：末尾二因子の交換と分離の両立を帰納的に比較する。
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

attribute [local implicit_reducible] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct

/-- 概要：末尾交換後の族を、先頭を固定した尾の交換で定義する（Berger–Moerdijk §1）。
方針：先頭は元の値とし、尾の添字に最後の隣接互換を適用する。
規約：元の族の入力数は n+3。
使われ方：末尾交換の再帰で対象の等式による移送を明示する。 -/
def tensorFamilyLastSwapTail (n : ℕ) (V : Fin (n + 3) → Complex A) :
    Fin (n + 3) → Complex A :=
  Fin.cases (V 0) (fun i => V (adjacentTransposition (Fin.last n) i).succ)

attribute [local implicit_reducible] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyLastSwapTail

/-- 概要：先頭と尾で記述した末尾交換は元の族の最後の隣接互換による引き戻しと一致する（Berger–Moerdijk §1）。
方針：先頭では固定点の式、尾ではずらした隣接互換の式を使う。
規約：族全体の等式として比較する。
使われ方：入力族の比較補題で二種類の末尾交換の記述を結ぶ。 -/
lemma tensorFamilyLastSwapTail_eq (n : ℕ) (V : Fin (n + 3) → Complex A) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyLastSwapTail n V =
      fun i => V (adjacentTransposition (Fin.last (n + 1)) i) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · change V 0 = V (adjacentTransposition (Fin.last (n + 1)) 0)
    exact congrArg V (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.adjacentLast_prefix (n + 1) 0).symm
  · change V (adjacentTransposition (Fin.last n) j).succ =
      V (adjacentTransposition (Fin.last (n + 1)) j.succ)
    exact congrArg V (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.adjacentLast_succ n j).symm

/-- 概要：先頭と尾で記述した末尾交換のテンソル対象を先頭と尾のテンソルに分ける（Berger–Moerdijk §1）。
方針：有限テンソルの一段の再帰と Fin.cases の計算則を使う。
規約：先頭は元の複体のまま保つ。
使われ方：尾の交換の whisker の終域を分離同型の始域へ同定する。 -/
lemma tensorFamilyLastSwapTail_source_obj (n : ℕ) (V : Fin (n + 3) → Complex A) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily (n + 3) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyLastSwapTail n V) =
      V 0 ⊗ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily (n + 2) (fun i => V (adjacentTransposition (Fin.last n) i).succ) := by
  change Fin.cases (V 0) (fun i => V (adjacentTransposition (Fin.last n) i).succ) 0 ⊗
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily (n + 2) (fun j =>
        Fin.cases (V 0) (fun i => V (adjacentTransposition (Fin.last n) i).succ) j.succ) = _
  simp only [Fin.cases_zero, Fin.cases_succ]

/-- 概要：先頭と尾で記述した末尾交換は前半の入力を保つ（Berger–Moerdijk §1）。
方針：先頭と残りの前半で場合分けし、尾の交換の固定点の式を使う。
規約：前半は二回の castSucc で指定する。
使われ方：分離の終域の前半を元の有限テンソルへ同定する。 -/
lemma tensorFamilyLastSwapTail_prefix (n : ℕ) (V : Fin (n + 3) → Complex A)
    (i : Fin (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyLastSwapTail n V i.castSucc.castSucc = V i.castSucc.castSucc := by
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · change V (adjacentTransposition (Fin.last n) j.castSucc.castSucc).succ =
      V j.castSucc.castSucc.succ
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.adjacentLast_prefix]

/-- 概要：先頭と尾で記述した末尾交換は最後から二番目を最後へ送る（Berger–Moerdijk §1）。
方針：尾の交換の最後から二番目での値を使う。
規約：元の族の最後の値を返す。
使われ方：交換後の分離された二因子の左側を同定する。 -/
lemma tensorFamilyLastSwapTail_penultimate (n : ℕ) (V : Fin (n + 3) → Complex A) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyLastSwapTail n V (Fin.last (n + 1)).castSucc = V (Fin.last (n + 2)) := by
  change V (adjacentTransposition (Fin.last n) (Fin.last n).castSucc).succ = _
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.adjacentLast_penultimate]
  rfl

/-- 概要：先頭と尾で記述した末尾交換は最後を最後から二番目へ送る（Berger–Moerdijk §1）。
方針：尾の交換の最後での値を使う。
規約：元の族の最後から二番目の値を返す。
使われ方：交換後の分離された二因子の右側を同定する。 -/
lemma tensorFamilyLastSwapTail_last (n : ℕ) (V : Fin (n + 3) → Complex A) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyLastSwapTail n V (Fin.last (n + 2)) = V (Fin.last (n + 1)).castSucc := by
  change V (adjacentTransposition (Fin.last n) (Fin.last (n + 1))).succ = _
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.adjacentLast_last]
  rfl

/-- 概要：先頭と尾で記述した末尾交換の分離の終域は前半と交換した末尾の対である（Berger–Moerdijk §1）。
方針：前半と末尾二位置の計算を有限テンソルへ適用する。
規約：前半 n+1 入力の順序を保つ。
使われ方：族の比較補題で分離の両方の終域を同じ対象へ移す。 -/
lemma tensorFamilyLastSwapTail_output_obj (n : ℕ) (V : Fin (n + 3) → Complex A) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily (n + 1) (fun i => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyLastSwapTail n V i.castSucc.castSucc) ⊗
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyLastSwapTail n V (Fin.last (n + 1)).castSucc ⊗
          _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyLastSwapTail n V (Fin.last (n + 2))) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily (n + 1) (fun i => V i.castSucc.castSucc) ⊗
        (V (Fin.last (n + 2)) ⊗ V (Fin.last (n + 1)).castSucc) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyLastSwapTail_prefix, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyLastSwapTail_penultimate,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyLastSwapTail_last]

/-- 概要：末尾交換後の分離を先頭と尾で記述した族の分離へ移す（Berger–Moerdijk §1）。
方針：入力族の等式と分離同型の比較補題を用いる。
規約：始域は先頭と交換後の尾のテンソル、終域は元の前半と交換した末尾の対。
使われ方：末尾交換と分離の可換性の帰納法で尾への制限を使える形にする。 -/
lemma tensorFamilySplitLastTwo_lastSwap_succ_compare (n : ℕ)
    (V : Fin (n + 3) → Complex A) :
    eqToHom (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily_adjacentSucc_obj (n + 1) V (Fin.last n)).symm ≫
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLastTwo (n + 1)
          (fun i => V (adjacentTransposition (Fin.last (n + 1)) i))).hom ≫
        eqToHom (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily_lastSwap_output_obj (n + 1) V) =
      eqToHom (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyLastSwapTail_source_obj n V).symm ≫
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLastTwo (n + 1) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyLastSwapTail n V)).hom ≫
        eqToHom (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyLastSwapTail_output_obj n V) := by
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLastTwo_compare (n + 1) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyLastSwapTail_eq n V)
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyLastSwapTail_source_obj n V)
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily_adjacentSucc_obj (n + 1) V (Fin.last n))
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyLastSwapTail_output_obj n V) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily_lastSwap_output_obj (n + 1) V)

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
