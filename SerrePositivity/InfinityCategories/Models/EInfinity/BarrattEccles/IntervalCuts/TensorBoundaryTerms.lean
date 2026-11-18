module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.TensorVectors
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.IntervalBoundary

/-!
模型。文献の定義との比較は後で
# 区間テンソルの因子ごとの境界項

概要：Berger–Fresse §2.2.7 の微分検証に使うテンソルの各因子の境界項を定義する。
方針：指定した因子を微分し、それ以前の次数から Koszul 符号を再帰的に掛ける。
規約：右括弧の整数コチェインのテンソルを使い、零因子には境界項がない。
使われ方：切断の出力の境界を削除微分の有限和と比較する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers
open scoped _root_.BigOperators

variable (A : Type u) [CommRing A]

/-- 概要：斉次純粋テンソルの微分の元での Leibniz 公式（BF §2.2.7）。
方針：既存の全テンソルの微分公式を純粋テンソルで評価する。
規約：第二項は第一因子の整数次数の Koszul 符号を持つ。
使われ方：反復テンソルの境界を因子ごとの和へ展開する帰納段階。 -/
lemma tensorPair_d_apply (P Q : Complex A) (r s t : ℤ) (h : r + s = t)
    (x : P.X r) (y : Q.X s) :
    (P ⊗ Q).d t (t + 1) (ιTensorObj P Q r s t h (x ⊗ₜ[A] y)) =
      ιTensorObj P Q (r + 1) s (t + 1) (by omega) (P.d r (r + 1) x ⊗ₜ[A] y) +
      r.negOnePow • ιTensorObj P Q r (s + 1) (t + 1) (by omega)
        (x ⊗ₜ[A] Q.d s (s + 1) y) := by
  have hd := SerrePositivity.ιTensorObj_cochainTensor_d P Q r s t h
  change ιTensorObj P Q r s t h ≫ (P ⊗ Q).d t (t + 1) = _ at hd
  have he := congrArg (fun f => f (x ⊗ₜ[A] y)) hd
  simpa [ModuleCat.comp_apply, ModuleCat.MonoidalCategory.whiskerRight_apply,
    ModuleCat.MonoidalCategory.whiskerLeft_apply, Units.smul_def] using! he

/-- 概要：区間テンソルの指定因子の符号付き境界項（BF §2.2.7）。
方針：先頭ならその因子を微分し、後続なら先頭を残してその次数の符号を掛ける。
規約：結果の整数次数は元の総次数の負に一を足したもの。
使われ方：反復テンソル生成元の境界の全有限和。 -/
def tensorBoundaryTerm : (n : ℕ) → (f : Fin n → _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.Simplex) → Fin n →
    (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) n).X (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree n f : ℤ) + 1)
  | 0, _, k => Fin.elim0 k
  | n + 1, f, k => Fin.cases
      (ιTensorObj (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) n) (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.simplexDegree (f 0) : ℤ) + 1)
        (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree n (fun i => f i.succ) : ℤ)) (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree (n + 1) f : ℤ) + 1)
        (by simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree, Nat.cast_add]; omega)
        ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A).d (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.simplexDegree (f 0) : ℤ)) (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.simplexDegree (f 0) : ℤ) + 1)
          (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceVector A (f 0)) ⊗ₜ[A] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVector A n (fun i => f i.succ)))
      (fun j => (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.simplexDegree (f 0) : ℤ)).negOnePow •
        ιTensorObj (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) n) (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.simplexDegree (f 0) : ℤ))
          (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree n (fun i => f i.succ) : ℤ) + 1)
          (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree (n + 1) f : ℤ) + 1)
          (by simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree, Nat.cast_add]; omega)
          (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceVector A (f 0) ⊗ₜ[A] tensorBoundaryTerm n (fun i => f i.succ) j)) k

/-- 概要：反復テンソル生成元の微分は各因子の境界の有限和（BF §2.2.7）。
方針：二因子 Leibniz 公式、帰納法、テンソルの有限和への分配を使う。
規約：任意の出力族と空テンソルを含み、符号は定義済みの Koszul 符号。
使われ方：切断作用の微分保存の出力側を全削除項へ照合する。 -/
lemma tensorVector_d (n : ℕ) (f : Fin n → _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.Simplex) :
    (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) n).d (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree n f : ℤ)) (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree n f : ℤ) + 1)
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVector A n f) = ∑ k : Fin n, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorBoundaryTerm A n f k := by
  induction n with
  | zero =>
    change ((HomologicalComplex.single (ModuleCat A) (.up ℤ) 0).obj
      (𝟙_ (ModuleCat A))).d 0 1 _ = _
    rw [single_obj_d]
    simp
  | succ n ih =>
    change ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) ⊗ power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) n).d
      (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree (n + 1) f : ℤ)) (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree (n + 1) f : ℤ) + 1)
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVector A (n + 1) f) = _
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVector, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorPair_d_apply, ih]
    simp only [Fin.sum_univ_succ, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorBoundaryTerm, Fin.cases_zero, Fin.cases_succ,
      TensorProduct.tmul_sum, map_sum, Finset.smul_sum]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
