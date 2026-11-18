module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.CompositionAdjacentOutput
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.ContextBlockSwapValues

/-!
模型。文献の定義との比較は後で
# 反復合成の隣接交換の出力の値

概要：Berger–Moerdijk §1 の反復合成の出力の全単射を四区間で記述する。
方針：末尾交換を中央のブロック交換へ移し、それ以外は最後の入力を分離して帰納する。
規約：交換位置より前の arity の和を前方の長さとする。
使われ方：先頭から再帰するテンソル族のブロック交換との同定に用いる。
-/

@[expose] public section

noncomputable section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.SerrePositivity.Coxeter
open scoped _root_.BigOperators

/-- 概要：隣接する二入力より前のブロックの総長を指定する（Berger–Moerdijk §1）。
方針：交換位置の値より小さい標準有限集合で和を取る。
規約：n+1 個のブロックと n 個の隣接交換位置を用いる。
使われ方：出力の全単射の四区間の境界となる。 -/
def operadAdjacentPrefixLength (n : ℕ) (s : Fin (n + 1) → ℕ) (i : Fin n) : ℕ :=
  ∑ j : Fin i.val, s ⟨j.val, by omega⟩

/-- 概要：末尾の隣接交換より前の総長は末尾二入力を除いた和である（Berger–Moerdijk §1）。
方針：交換位置の値と標準有限集合への埋め込みを計算する。
規約：入力は n+2 個。
使われ方：末尾交換の出力の値を一般の式へ合わせる。 -/
lemma operadAdjacentPrefixLength_last (n : ℕ) (s : Fin (n + 2) → ℕ) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadAdjacentPrefixLength (n + 1) s (Fin.last n) =
      ∑ j : Fin n, s j.castSucc.castSucc := rfl

/-- 概要：末尾を固定する隣接交換の前方の総長は末尾を除いても変わらない（Berger–Moerdijk §1）。
方針：交換位置と和の各項の値を計算する。
規約：前半の族は castSucc による制限。
使われ方：出力の値の帰納段階で区間の境界を保つ。 -/
lemma operadAdjacentPrefixLength_castSucc (n : ℕ) (s : Fin (n + 2) → ℕ) (i : Fin n) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadAdjacentPrefixLength (n + 1) s i.castSucc =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadAdjacentPrefixLength n (fun j => s j.castSucc) i := rfl

/-- 概要：末尾二入力の交換の出力の値を四区間で計算する（Berger–Moerdijk §1）。
方針：前方を固定する尾の交換を中央の二ブロック交換へ直し、その値の式を使う。
規約：前方は末尾二入力以外、後方は未代入入力 k 個。
使われ方：任意の隣接交換の出力の値の帰納法の末尾の場合となる。 -/
lemma operadLastTwoOutputEquiv_val (n k : ℕ) (s : Fin (n + 2) → ℕ)
    (x : Fin ((∑ j, s j) + k)) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadLastTwoOutputEquiv n k s x).val =
      let p := ∑ j : Fin n, s j.castSucc.castSucc
      let a := s (Fin.last n).castSucc
      let b := s (Fin.last (n + 1))
      if x.val < p then x.val else
      if x.val < p + a then x.val + b else
      if x.val < p + a + b then x.val - a else x.val := by
  let p := ∑ j : Fin n, s j.castSucc.castSucc
  let a := s (Fin.last n).castSucc
  let b := s (Fin.last (n + 1))
  have hlen : ((p + k) + a) + b = (∑ j, s j) + k := by
    have h := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.lastTwoComposeOutput_eq n k s
    dsimp [p, a, b]
    omega
  let y : Fin (((p + k) + a) + b) := finCongr hlen.symm x
  have h := congrArg (fun e => (e y).val) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadContextBlockSwap_tail p k a b)
  have hv := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadContextBlockSwap_val p k a b y
  rw [h] at hv
  exact hv

/-- 概要：任意の隣接交換の反復合成の出力は中央の二ブロックだけを交換する（Berger–Moerdijk §1）。
方針：末尾の交換の四区間の式を使い、末尾固定の場合は arity の移送が値を保つことから帰納する。
規約：二ブロックの前方と後方および各ブロックの内部順序は保つ。
使われ方：テンソル族のブロック交換との点ごとの比較に用いる。 -/
lemma operadCompositionAdjacentOutput_val (n k : ℕ) (s : Fin (n + 1) → ℕ)
    (i : Fin n) (x : Fin ((∑ j, s j) + k)) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadCompositionAdjacentOutput n k s i x).val =
      let p := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadAdjacentPrefixLength n s i
      let a := s i.castSucc
      let b := s i.succ
      if x.val < p then x.val else
      if x.val < p + a then x.val + b else
      if x.val < p + a + b then x.val - a else x.val := by
  induction n generalizing k with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadCompositionAdjacentOutput_last]
      exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadLastTwoOutputEquiv_val n k s x
    · rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadCompositionAdjacentOutput_castSucc]
      exact ih (k + s (Fin.last (n + 1))) (fun j => s j.castSucc) j
        (finCongr (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.oneSlotComposeOutput_eq (n + 1) k s).symm x)

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
