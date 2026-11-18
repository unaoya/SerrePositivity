module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.TensorVectors

/-!
模型。文献の定義との比較は後で
# 区間切断の実際のテンソル成分

概要：Berger–Fresse §2.2.6 の切断値を正規化区間のテンソルの次数成分へ送る。
方針：出力総次数の証明で全ての項の次数を揃え、全射語基底から線形延長する。
規約：まだ微分保存を仮定しない成分写像であり、複体射への束ねは後に行う。
使われ方：χ の区間余演算の微分保存とオペラッドの公理の検証。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.CategoryTheory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers
open scoped _root_.BigOperators

variable (A : Type u) [CommRing A]

/-- 概要：語の辺への作用を実際の区間のテンソル成分へ送る（BF §2.2.6）。
方針：各非退化切断の出力テンソルを整数符号で重み付けして足す。
規約：語次数 d と入力辺の次数一の和を負の整数次数へ移す。
使われ方：余演算の辺での成分値。 -/
def edgeComponentOnWord {n d : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d) :
    (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) n).X (-((d + 1 : ℕ) : ℤ)) :=
  ∑ p : Fin (n + d), if h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u.val p then
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeSign u.val p : A) •
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVectorOfDegree A n (d + 1) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput u p) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput_tupleDegree u p h)
    else 0

/-- 概要：語の頂点への作用を実際の区間テンソルへ送る（BF §2.2.6）。
方針：次数零なら各出力に同じ頂点を置き、正次数は零とする。
規約：語次数 d の出力の整数次数は −d。
使われ方：余演算の二つの端点での成分値。 -/
def vertexComponentOnWord {n d : ℕ} (_u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d) (b : Fin 2) :
    (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) n).X (-(d : ℤ)) :=
  if h : d = 0 then _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVectorOfDegree A n d (fun _ => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex b)
    (by rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex_tupleDegree, h]) else 0

/-- 概要：実際の辺の切断成分を全射語加群へ線形延長する（BF §2.2.6）。
方針：全射語基底の像を辺の符号付きテンソル和とする。
規約：微分保存はまだ入力に含めない。
使われ方：余演算の複体射の辺での線形成分。 -/
def edgeComponent (n d : ℕ) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.degreeModule A n d →ₗ[A]
    (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) n).X (-((d + 1 : ℕ) : ℤ)) :=
  (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A n d).constr A (fun v => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeComponentOnWord A v.down)

/-- 概要：実際の頂点の切断成分を全射語加群へ線形延長する（BF §2.2.6）。
方針：全射語基底の像を同じ頂点のテンソルまたは零とする。
規約：両端点を同じ定義で扱う。
使われ方：余演算の複体射の端点での線形成分。 -/
def vertexComponent (n d : ℕ) (b : Fin 2) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.degreeModule A n d →ₗ[A]
    (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) n).X (-(d : ℤ)) :=
  (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A n d).constr A (fun v => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexComponentOnWord A v.down b)

/-- 概要：辺成分の基底評価は実際の切断テンソルの有限和（BF §2.2.6）。
方針：基底による線形延長を評価する。
規約：任意の可換環・全 arity・全語次数。
使われ方：微分保存を全射語基底で検証する。 -/
@[simp] lemma edgeComponent_basis {n d : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeComponent A n d (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A n d (ULift.up u)) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeComponentOnWord A u :=
  Module.Basis.constr_basis (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A n d) A _ _

/-- 概要：頂点成分の基底評価は頂点のテンソル値（BF §2.2.6）。
方針：基底による線形延長を評価する。
規約：零頂点と一頂点を含む。
使われ方：端点での微分保存と余代数射性。 -/
@[simp] lemma vertexComponent_basis {n d : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d) (b : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexComponent A n d b (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A n d (ULift.up u)) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexComponentOnWord A u b :=
  Module.Basis.constr_basis (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A n d) A _ _

/-- 概要：必要次数を超える語の実際の辺への作用は零（BF §2.2）。
方針：非退化な切断なら d+1≤n であることにより各項を消す。
規約：テンソルの基底の独立性や相殺を仮定しない。
使われ方：高次数の余演算を成分ごとに消去する。 -/
lemma edgeComponentOnWord_eq_zero_of_degree {n d : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d)
    (hd : n < d + 1) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeComponentOnWord A u = 0 := by
  apply Finset.sum_eq_zero
  intro p _
  rw [dite_eq_right (fun h => (not_le_of_gt hd) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edge_degree_bound u p h))]

/-- 概要：正次数の語の実際の頂点への作用は零（BF §2.2）。
方針：頂点成分の次数零の分岐を排除する。
規約：任意の arity。
使われ方：端点が余代数射となることの正次数の分岐。 -/
lemma vertexComponentOnWord_eq_zero_of_positive {n d : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d)
    (hd : 0 < d) (b : Fin 2) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexComponentOnWord A u b = 0 := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexComponentOnWord
  rw [dite_eq_right (by omega : d ≠ 0)]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
