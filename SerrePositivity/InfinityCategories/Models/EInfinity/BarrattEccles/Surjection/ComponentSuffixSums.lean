module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.ComponentPaths
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Intervals

/-!
模型。文献の定義との比較は後で
# 成分列の交換指数と後続成分の有限和

概要：Berger–Fresse §1.5.6 の成分経路の再帰的交換指数を明示的な有限和へ直す。
方針：成分列で帰納して後続水平次数の和を取り、ofFn の drop を自然数区間へ移す。
規約：成分次数は非負整数。
使われ方：候補経路の shuffle 符号と元の合成符号の指数を照合する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：再帰的な成分交換指数は各垂直成分×全後続水平成分の和（BF §1.5.6）。
方針：先頭対の寄与を分離して有限添字の和に帰納する。
規約：同じ対の水平成分も後続に含む。
使われ方：成分経路の符号を合成語の符号指数の形へ直す。 -/
lemma _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.blockExponent_eq_sum (xs : List (ℕ × ℕ)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.blockExponent xs = ∑ i : Fin xs.length,
      xs[i.val].1 * (((xs.drop i.val).map Prod.snd).sum) := by
  induction xs with
  | nil => simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.blockExponent, List.length_nil, Fin.sum_univ_zero]
  | cons p xs ih =>
    rcases p with ⟨v, h⟩
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.blockExponent]
    erw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, List.getElem_cons_zero, List.drop_zero, List.map_cons,
      List.sum_cons, Fin.val_succ, List.getElem_cons_succ, List.drop_succ_cons]
    rw [← ih]
    ac_rfl

/-- 概要：有限関数から作った成分列の交換指数（BF §1.5.6）。
方針：成分列の長さと元の有限型の等式で和を付け替える。
規約：添字の値を保つ移送だけを使う。
使われ方：具体的な合成次数列を元の出現添字で評価する。 -/
lemma _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.blockExponent_ofFn {t : ℕ} (f : Fin t → ℕ × ℕ) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.blockExponent (List.ofFn f) = ∑ i : Fin t,
      (f i).1 * ((((List.ofFn f).drop i.val).map Prod.snd).sum) := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.blockExponent_eq_sum]
  apply Fintype.sum_equiv (finCongr (show (List.ofFn f).length = t from List.length_ofFn))
  intro i
  simp only [List.getElem_ofFn]
  rfl

/-- 概要：有限関数の列の後続和は対応する自然数区間の和（BF §1.5.6）。
方針：語長と開始位置で帰納し、区間の平行移動で添字を戻す。
規約：開始が語長以上の場合は両側とも空和。
使われ方：後続水平成分のリスト和を行次数の区間和へ直す。 -/
lemma sum_drop_ofFn_nat (f : ℕ → ℕ) (t a : ℕ) :
    ((List.ofFn (fun i : Fin t => f i.val)).drop a).sum =
      ∑ i ∈ Finset.Ico a t, f i := by
  induction t generalizing f a with
  | zero => simp
  | succ t ih =>
    cases a with
    | zero =>
      rw [List.drop_zero, List.sum_ofFn, Fin.sum_univ_eq_sum_range f (t + 1)]
      rw [Nat.Ico_zero_eq_range]
    | succ a =>
      rw [List.ofFn_succ, List.drop_succ_cons]
      change ((List.ofFn (fun i : Fin t => f (i.val + 1))).drop a).sum = _
      rw [ih (fun j => f (j + 1)) a]
      exact Finset.sum_Ico_add' f a t 1

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
