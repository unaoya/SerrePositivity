module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorSwapNaturality
public import SerrePositivity.GroupTheory.Coxeter.FirstToLast

/-!
模型。文献の定義との比較は後で
# 異なる複体の有限テンソル族の隣接交換

概要：Berger–Moerdijk §1 の外側等変性で、内側演算の隣接する二因子を交換する同型を構成する。
方針：先頭の交換は結合子と Koszul 対称性で与え、他の位置は尾の交換を再帰する。
規約：交換後の対象は、隣接互換で添字を引き戻した同じ有限テンソルの定義を使う。
使われ方：オペラッド合成の外側等変性を隣接互換から証明する。
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

/-- 概要：先頭の隣接互換は先頭の入力を二番目の入力へ送る（Berger–Moerdijk §1）。
方針：隣接互換の定義の二点の交換を評価する。
規約：入力位置は 0 始まり。
使われ方：先頭の二因子のテンソル交換の終域を同定する。 -/
lemma adjacentFirst_zero (n : ℕ) :
    adjacentTransposition (0 : Fin (n + 1)) 0 = (1 : Fin (n + 2)) := by
  change Equiv.swap (0 : Fin (n + 2)) 1 0 = 1
  exact Equiv.swap_apply_left _ _

/-- 概要：先頭の隣接互換は二番目の入力を先頭の入力へ送る（Berger–Moerdijk §1）。
方針：隣接互換の定義の二点の交換を評価する。
規約：少なくとも二つの入力を持つ。
使われ方：先頭の二因子のテンソル交換の終域を同定する。 -/
lemma adjacentFirst_one (n : ℕ) :
    adjacentTransposition (0 : Fin (n + 1)) 1 = (0 : Fin (n + 2)) := by
  change Equiv.swap (0 : Fin (n + 2)) 1 1 = 0
  exact Equiv.swap_apply_right _ _

/-- 概要：先頭の隣接互換は三番目以降の入力を固定する（Berger–Moerdijk §1）。
方針：入力位置が交換する二点のいずれとも異なることを使う。
規約：三番目以降の入力を二回の `Fin.succ` で表す。
使われ方：先頭の二因子以外のテンソル族を保つ。 -/
lemma adjacentFirst_tail (n : ℕ) (i : Fin n) :
    adjacentTransposition (0 : Fin (n + 1)) i.succ.succ = i.succ.succ := by
  change Equiv.swap (0 : Fin (n + 2)) 1 i.succ.succ = _
  apply Equiv.swap_apply_of_ne_of_ne
  · exact Fin.succ_ne_zero _
  · intro h
    have hv := congrArg Fin.val h
    dsimp at hv
    have hm : 1 % (n + 1 + 1) = 1 := Nat.mod_eq_of_lt (by omega)
    omega

/-- 概要：先頭の二因子を交換した有限テンソルの対象を具体化する（Berger–Moerdijk §1）。
方針：先頭二つと残りの族で隣接互換を評価する。
規約：残りの族の順序は変えない。
使われ方：結合子と対称性の合成の終域を有限テンソルの対象へ戻す。 -/
lemma tensorFamily_firstSwap_obj (n : ℕ) (V : Fin (n + 2) → Complex A) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily (n + 2) (fun i => V (adjacentTransposition (0 : Fin (n + 1)) i)) =
      V 1 ⊗ (V 0 ⊗ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun i => V i.succ.succ)) := by
  change V (adjacentTransposition (0 : Fin (n + 1)) 0) ⊗
    (V (adjacentTransposition (0 : Fin (n + 1)) 1) ⊗
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun i => V (adjacentTransposition (0 : Fin (n + 1)) i.succ.succ))) = _
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.adjacentFirst_zero, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.adjacentFirst_one, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.adjacentFirst_tail]

/-- 概要：尾の置換は先頭を固定する有限テンソルの対象として表せる（Berger–Moerdijk §1）。
方針：ずらした置換を先頭と尾で評価する。
規約：尾の入力の置換は任意の置換とする。
使われ方：先頭以外の位置で隣接交換を再帰的に構成する。 -/
lemma tensorFamily_shiftPermutation_obj (n : ℕ) (V : Fin (n + 1) → Complex A)
    (σ : Equiv.Perm (Fin n)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily (n + 1) (fun i => V (shiftPerm σ i)) =
      V 0 ⊗ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun i => V (σ i).succ) := by
  change V (shiftPerm σ 0) ⊗ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun i => V (shiftPerm σ i.succ)) = _
  simp only [shiftPerm_zero, shiftPerm_succ]

/-- 概要：異なる複体の有限テンソル族の先頭二因子を交換する（Berger–Moerdijk §1）。
方針：結合子で最初の二因子を括り、Koszul 対称性で交換してから括弧を戻す。
規約：終域は先頭の隣接互換によって引き戻した有限族。
使われ方：全ての位置の隣接交換を再帰的に構成する基底となる。 -/
def tensorFamilySwapFirstIso (n : ℕ) (V : Fin (n + 2) → Complex A) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily (n + 2) V ≅
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily (n + 2) (fun i => V (adjacentTransposition (0 : Fin (n + 1)) i)) :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorTripleSwapIso (V 0) (V 1) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun i => V i.succ.succ)) ≪≫
    eqToIso (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily_firstSwap_obj n V).symm

/-- 概要：異なる複体の有限テンソル族の任意の隣接二因子を交換する（Berger–Moerdijk §1）。
方針：先頭の交換と先頭の因子を保つ尾の交換で再帰する。
規約：n+1 個の因子に n 個の隣接交換を添字付ける。
使われ方：自由代数の外側等変性で入力の生成射の因子を並べ替える。 -/
def tensorFamilyAdjacentIso : ∀ (n : ℕ) (V : Fin (n + 1) → Complex A) (i : Fin n),
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily (n + 1) V ≅ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily (n + 1) (fun j => V (adjacentTransposition i j))
  | 0, _, i => Fin.elim0 i
  | n + 1, V, i => by
    refine Fin.cases (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySwapFirstIso n V) (fun j => ?_) i
    have h := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily_shiftPermutation_obj (n + 1) V (adjacentTransposition j)
    rw [shiftPerm_adjacent] at h
    exact whiskerLeftIso (V 0) (tensorFamilyAdjacentIso n (fun i => V i.succ) j) ≪≫ eqToIso h.symm

/-- 概要：尾の隣接交換後の対象を先頭と尾に分離する（Berger–Moerdijk §1）。
方針：先頭を固定するずらした置換の対象の式を隣接互換へ適用する。
規約：先頭の因子は変えない。
使われ方：隣接交換の再帰の射を明示する。 -/
lemma tensorFamily_adjacentSucc_obj (n : ℕ) (V : Fin (n + 2) → Complex A) (i : Fin n) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily (n + 2) (fun j => V (adjacentTransposition i.succ j)) =
      V 0 ⊗ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily (n + 1) (fun j => V (adjacentTransposition i j).succ) := by
  have h := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily_shiftPermutation_obj (n + 1) V (adjacentTransposition i)
  rw [shiftPerm_adjacent] at h
  exact h

/-- 概要：先頭の隣接交換の射は先頭二因子の交換の射である（Berger–Moerdijk §1）。
方針：再帰定義の先頭の場合を評価する。
規約：対象の比較の移送を含む。
使われ方：生成射の隣接交換の自然性の帰納法の基底に用いる。 -/
lemma tensorFamilyAdjacentIso_zero (n : ℕ) (V : Fin (n + 2) → Complex A) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyAdjacentIso (n + 1) V 0).hom = (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySwapFirstIso n V).hom := rfl

/-- 概要：尾の隣接交換の射は尾の交換と対象の移送の合成である（Berger–Moerdijk §1）。
方針：再帰定義の尾の場合を評価し、対象の比較の証明を一意性で同一視する。
規約：先頭の因子を保った whisker を用いる。
使われ方：再帰の定義を展開せず生成射の自然性を帰納的に証明する。 -/
lemma tensorFamilyAdjacentIso_succ (n : ℕ) (V : Fin (n + 2) → Complex A) (i : Fin n) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyAdjacentIso (n + 1) V i.succ).hom =
      (V 0 ◁ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyAdjacentIso n (fun j => V j.succ) i).hom) ≫
        eqToHom (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily_adjacentSucc_obj n V i).symm := rfl

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
