module

public import SerrePositivity.EInfinity.IntervalCuts.EndpointTensors
public import SerrePositivity.EInfinity.IntervalCuts.TensorBoundaryValues

/-!
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

namespace SerrePositivity.EInfinity.IntervalCuts

open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers

variable (A : Type u) [CommRing A]

/-- 概要：辺因子の境界項は前方次数符号付きの終点置換−始点置換（BF §2.2.7）。
方針：先頭では辺の微分を使い、後続では再帰的な符号を前方次数へ足す。
規約：指定した出力因子が辺である証明を要求する。
使われ方：実際のテンソル境界と語の二つの削除項を比較する。 -/
lemma tensorBoundaryTerm_eq_endpoints (n : ℕ) (f : Fin n → Simplex) (k : Fin n)
    (hf : f k = edge) : tensorBoundaryTerm A n f k =
      (-1 : ℤ) ^ prefixDegree n f k •
        (endpointTensor A n f k hf 1 - endpointTensor A n f k hf 0) := by
  induction n with
  | zero => exact Fin.elim0 k
  | succ n ih =>
    obtain ⟨s, g, rfl⟩ := Fin.exists_cons f
    revert hf
    refine Fin.cases ?_ (fun j => ?_) k
    · intro hf
      change s = edge at hf
      subst s
      rw [prefixDegree_zero, pow_zero, one_smul,
        endpointTensor_zero_cons, endpointTensor_zero_cons]
      exact tensorBoundaryTerm_zero_edge A n g
    · intro hf
      change g j = edge at hf
      change (-(simplexDegree s : ℤ)).negOnePow •
        ιTensorObj (interval A) (power (interval A) n) (-(simplexDegree s : ℤ))
          (-(tupleDegree n g : ℤ) + 1)
          (-(tupleDegree (n + 1) (Fin.cons s g) : ℤ) + 1) _
          (faceVector A s ⊗ₜ[A] tensorBoundaryTerm A n g j) = _
      rw [ih g j hf, endpointTensor_succ_cons, endpointTensor_succ_cons]
      simp only [prefixDegree_succ, Fin.cons_zero, Fin.cons_succ, pow_add,
        Units.smul_def, Int.negOnePow_neg, Int.coe_negOnePow_natCast,
        TensorProduct.tmul_smul, map_zsmul,
        TensorProduct.tmul_sub, map_sub, smul_smul]

end SerrePositivity.EInfinity.IntervalCuts
