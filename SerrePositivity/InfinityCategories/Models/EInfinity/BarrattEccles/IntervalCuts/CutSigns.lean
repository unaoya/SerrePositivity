module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeOutputs

/-!
模型。文献の定義との比較は後で
# Δ¹ の区間切断の符号

概要：Berger–Fresse §2.2.3–6 の区間長、置換符号、位置符号を一単体へ特殊化する。
方針：内側区間には次数一を加え、唯一の長い区間にも次数一を加える。
規約：色の昇順への交換の Koszul 指数と、内側区間の右端点の和を加える。
使われ方：辺の区間切断の各非零項の整数係数。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
open scoped _root_.BigOperators

/-- 概要：辺の切断区間の符号に使う長さ（BF §2.2.3）。
方針：内側区間は一、辺を含む区間も一だけ長さを増す。
規約：退化な切断でも長さを定義する。
使われ方：区間交換の Koszul 指数。 -/
def edgeIntervalLength {n l : ℕ} (u : Fin l → Fin n) (p i : Fin l) : ℕ :=
  (if _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u i then 1 else 0) + (if i = p then 1 else 0)

/-- 概要：区間を色順へ並べる交換の指数（BF §2.2.4）。
方針：逆転する位置対に、それぞれの区間長の積を足す。
規約：同じ色の区間の順序は変えない。
使われ方：辺の切断の置換符号。 -/
def edgePermutationExponent {n l : ℕ} (u : Fin l → Fin n) (p : Fin l) : ℕ :=
  ∑ i : Fin l, ∑ j : Fin l,
    if i < j ∧ u j < u i then _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeIntervalLength u p i * _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeIntervalLength u p j else 0

/-- 概要：内側区間の右端点による位置符号の指数（BF §2.2.4）。
方針：切断点以後の内側区間の右端点は一、それより前は零。
規約：切断点自身を含める。
使われ方：辺の切断の位置符号。 -/
def edgePositionExponent {n l : ℕ} (u : Fin l → Fin n) (p : Fin l) : ℕ :=
  ∑ i : Fin l, if _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u i ∧ p ≤ i then 1 else 0

/-- 概要：辺の切断項の整数符号（BF §2.2.4–6）。
方針：交換指数と位置指数の和で −1 を累乗する。
規約：任意の係数環へ整数から移す。
使われ方：正規化した各出力テンソルの係数。 -/
def edgeSign {n l : ℕ} (u : Fin l → Fin n) (p : Fin l) : ℤ :=
  (-1) ^ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgePermutationExponent u p + _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgePositionExponent u p)

/-- 概要：非退化な切断で辺を含む区間は内側区間ではない（BF §2.2.1）。
方針：辺を持つ色の一意性から後の出現を排除する。
規約：語の全射性は要求しない。
使われ方：切断点で区間長が二となる退化項を排除する。 -/
lemma not_caesura_pivot {n l : ℕ} {u : Fin l → Fin n} {p : Fin l}
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u p) : ¬ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u p := by
  rintro ⟨j, hpj, hj⟩
  have he := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.pivot_unique h j hj
  exact (ne_of_gt hpj) he

/-- 概要：非退化な切断で辺を含む区間の符号長は一（BF §2.2.3）。
方針：切断点が内側区間でないことを使う。
規約：退化な切断では二となる場合がある。
使われ方：辺の微分の切断点の符号比較。 -/
lemma edgeIntervalLength_pivot {n l : ℕ} {u : Fin l → Fin n} {p : Fin l}
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u p) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeIntervalLength u p p = 1 := by
  simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeIntervalLength, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.not_caesura_pivot h]

/-- 概要：色の置換は区間長を保つ（BF §2.2.3）。
方針：同じ色の後の出現の存在は置換で変わらない。
規約：位置と切断点は固定する。
使われ方：切断作用と出力テンソルの Koszul 置換の比較。 -/
lemma edgeIntervalLength_rename {n l : ℕ} (σ : Equiv.Perm (Fin n))
    (u : Fin l → Fin n) (p i : Fin l) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeIntervalLength (σ ∘ u) p i = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeIntervalLength u p i := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeIntervalLength, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesura_rename_iff]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
