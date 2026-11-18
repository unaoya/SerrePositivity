module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NormalizedInterval
public import SerrePositivity.CategoryTheory.Monoidal.TensorPower.Basic
public import SerrePositivity.DifferentialGraded.Complexes.Perturbation

/-!
模型。文献の定義との比較は後で
# 正規化区間の反復テンソルの斉次生成元

概要：Berger–Fresse §2.2.6 の出力基底族を実際の N_*(Δ¹) の反復テンソルへ送る。
方針：右括弧の反復テンソルへ各面の生成元を順に挿入する。
規約：零因子は次数零のテンソル単位の元一。
使われ方：切断作用の符号付き有限和の実際の値域。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers
open scoped _root_.BigOperators

/-- 概要：出力単体族の総鎖次数（BF §2.2.3）。
方針：右括弧のテンソルに合わせて先頭の次数と残りの次数を足す。
規約：空族の次数は零。
使われ方：反復テンソル生成元の次数の型付け。 -/
def tupleDegree : (n : ℕ) → (Fin n → _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.Simplex) → ℕ
  | 0, _ => 0
  | n + 1, f => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.simplexDegree (f 0) + tupleDegree n (fun i => f i.succ)

/-- 概要：再帰的な総次数は各出力次数の有限和（BF §2.2.3）。
方針：有限和を先頭と残りへ分けて帰納法を使う。
規約：空和も含む。
使われ方：切断の出力の総次数計算を反復テンソルへ移す。 -/
lemma tupleDegree_eq_sum (n : ℕ) (f : Fin n → _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.Simplex) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree n f = ∑ i : Fin n, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.simplexDegree (f i) := by
  induction n with
  | zero => simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree]
  | succ n ih => simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree, Fin.sum_univ_succ, ih]

variable (A : Type u) [CommRing A]

/-- 概要：各面の正規化生成元の右括弧テンソル（BF §2.2.6）。
方針：テンソル単位の元一から始め、斉次成分の包含で先頭の面を加える。
規約：総鎖次数の負が整数コチェイン次数。
使われ方：区間切断の各非退化出力の実際のテンソル値。 -/
def tensorVector : (n : ℕ) → (f : Fin n → _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.Simplex) →
    (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) n).X (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree n f : ℤ))
  | 0, _ => (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A)
  | n + 1, f =>
    ιTensorObj (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) n) (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.simplexDegree (f 0) : ℤ))
      (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree n (fun i => f i.succ) : ℤ)) (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree (n + 1) f : ℤ))
      (by simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree, Nat.cast_add]; omega)
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceVector A (f 0) ⊗ₜ[A] tensorVector n (fun i => f i.succ))

/-- 概要：総次数が指定された出力族のテンソル生成元（BF §2.2.6）。
方針：総次数の等式で実際の次数成分へ移す。
規約：移送は加群の等式の射。
使われ方：切断の全ての項の値域を一つの次数へ揃える。 -/
def tensorVectorOfDegree (n q : ℕ) (f : Fin n → _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.Simplex) (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree n f = q) :
    (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) n).X (-(q : ℤ)) :=
  eqToHom (congrArg (fun r : ℤ => (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) n).X r)
    (congrArg (fun r : ℕ => -(r : ℤ)) h)) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVector A n f)

/-- 概要：総次数をそのまま指定すれば移送は恒等（BF §2.2.6）。
方針：反射的な等式の射を消す。
規約：任意の出力族。
使われ方：具体的な出力で移送を計算する。 -/
@[simp] lemma tensorVectorOfDegree_refl (n : ℕ) (f : Fin n → _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.Simplex) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVectorOfDegree A n (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree n f) f rfl = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVector A n f := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVectorOfDegree, eqToHom_refl, ModuleCat.id_apply]

/-- 概要：非退化な辺の切断の出力族は総次数 d+1（BF §2.2.3）。
方針：再帰的総次数を有限和へ戻して既存の次数計算を使う。
規約：全 arity・全語次数。
使われ方：辺への余演算の全項を同じ次数成分へ送る。 -/
lemma edgeOutput_tupleDegree {n d : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d)
    (p : Fin (n + d)) (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u.val p) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree n (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput u p) = d + 1 := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree_eq_sum]
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput_total_degree u p h

/-- 概要：全出力が同じ頂点である族の総次数は零（BF §2.2.6）。
方針：各一元頂点集合の次数零を足す。
規約：空族も含む。
使われ方：頂点への余演算を次数零へ送る。 -/
lemma vertex_tupleDegree (n : ℕ) (b : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree n (fun _ => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex b) = 0 := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree_eq_sum]
  simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.simplexDegree, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
