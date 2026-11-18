module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EndpointTensors
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.TensorBoundaryValues

/-!
模型。文献の定義との比較は後で
# 各辺因子の境界の符号付き端点公式

概要：Berger–Fresse §2.2.7 の各因子の境界を実際の端点置換テンソルの差で表す。
方針：右括弧の再帰式を比較し、前方次数の和で全 Koszul 符号をまとめる。
規約：係数は整数の −1 冪、出力は元のテンソルの境界次数。
使われ方：左右の反復文字の削除と各辺の境界の符号付き値を一致させる。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers

variable (A : Type u) [CommRing A]

/-- 概要：辺因子の境界項は前方次数符号付きの終点置換−始点置換（BF §2.2.7）。
方針：先頭では辺の微分を使い、後続では再帰的な符号を前方次数へ足す。
規約：指定した出力因子が辺である証明を要求する。
使われ方：実際のテンソル境界と語の二つの削除項を比較する。 -/
lemma tensorBoundaryTerm_eq_endpoints (n : ℕ) (f : Fin n → _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.Simplex) (k : Fin n)
    (hf : f k = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edge) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorBoundaryTerm A n f k =
      (-1 : ℤ) ^ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.prefixDegree n f k •
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.endpointTensor A n f k hf 1 - _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.endpointTensor A n f k hf 0) := by
  induction n with
  | zero => exact Fin.elim0 k
  | succ n ih =>
    obtain ⟨s, g, rfl⟩ := Fin.exists_cons f
    revert hf
    refine Fin.cases ?_ (fun j => ?_) k
    · intro hf
      change s = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edge at hf
      subst s
      rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.prefixDegree_zero, pow_zero, one_smul,
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.endpointTensor_zero_cons, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.endpointTensor_zero_cons]
      exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorBoundaryTerm_zero_edge A n g
    · intro hf
      change g j = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edge at hf
      change (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.simplexDegree s : ℤ)).negOnePow •
        ιTensorObj (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) n) (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.simplexDegree s : ℤ))
          (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree n g : ℤ) + 1)
          (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree (n + 1) (Fin.cons s g) : ℤ) + 1) _
          (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceVector A s ⊗ₜ[A] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorBoundaryTerm A n g j) = _
      rw [ih g j hf, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.endpointTensor_succ_cons, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.endpointTensor_succ_cons]
      simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.prefixDegree_succ, Fin.cons_zero, Fin.cons_succ, pow_add,
        Units.smul_def, Int.negOnePow_neg, Int.coe_negOnePow_natCast,
        TensorProduct.tmul_smul, map_zsmul,
        TensorProduct.tmul_sub, map_sub, smul_smul]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
