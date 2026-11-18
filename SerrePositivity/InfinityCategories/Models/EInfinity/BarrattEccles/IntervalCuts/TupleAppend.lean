module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.TensorSwapVectors

/-!
模型。文献の定義との比較は後で
# 面の族の連結と arity の移送

概要：Berger–Fresse §2.2.6 の出力連結で必要な次数と有限添字の移送を整理する。
方針：族の次数を有限和へ直し、arity の等式による移送は等式消去で処理する。
規約：前半・後半とも空族を許す。
使われ方：実際の appendIso と面テンソルの連結の評価。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers

/-- 概要：連結した面の族の全次数は両族の全次数の和（BF §2.2.3）。
方針：全次数を有限和へ直し、和の入力集合を前後に分ける。
規約：空族の次数は零。
使われ方：appendIso の入力二次数と出力次数を一致させる。 -/
lemma tupleDegree_append {m n : ℕ} (f : Fin m → _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.Simplex) (g : Fin n → _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.Simplex) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree (m + n) (Fin.append f g) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree m f + _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree n g := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree_eq_sum, Fin.sum_univ_add, Fin.append_left, Fin.append_right]

/-- 概要：arity の等式で移した面の族の全次数は不変（BF §2.2.3）。
方針：arity の等式を消去する。
規約：有限添字の値の順序を保つ移送を使う。
使われ方：連結の再帰式に現れる自然数の結合順序の移送。 -/
lemma tupleDegree_arity_transport {m n : ℕ} (h : m = n) (f : Fin m → _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.Simplex) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree n (f ∘ Fin.cast h.symm) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree m f := by
  cases h
  rfl

/-- 概要：実際の面テンソルは arity の等式による反復テンソルの移送と両立（BF §2.2.6）。
方針：arity の等式を消去し、恒等射の成分を評価する。
規約：整数全次数は同じ指定値に保つ。
使われ方：appendIso の再帰式の終端の eqToHom を計算する。 -/
lemma tensorVectorAt_arity_transport (A : Type u) [CommRing A] {m n : ℕ}
    (h : m = n) (f : Fin m → _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.Simplex) (r : ℤ) (hf : -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree m f : ℤ) = r) :
    (eqToHom (congrArg (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A)) h)).f r (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVectorAt A m f r hf) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVectorAt A n (f ∘ Fin.cast h.symm) r
        (by rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree_arity_transport h f]; exact hf) := by
  cases h
  rfl

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
