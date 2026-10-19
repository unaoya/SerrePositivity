module

public import SerrePositivity.EInfinity.IntervalCuts.TensorDegreeTransport
public import SerrePositivity.EInfinity.IntervalCuts.TupleUpdates

/-!
# 一つの辺を端点へ置換した実際のテンソル

概要：Berger–Fresse §2.2.7 の辺の境界の各端点項を置換後の出力族のテンソルとして定義する。
方針：Function.update で一因子を置換し、次数が一つ下がる証明で境界成分へ移す。
規約：新たな抽象基底を仮定せず、既存の正規化生成元の反復テンソルを使う。
使われ方：因子境界を実際の削除語の出力族と比較する。
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

/-- 概要：指定した辺因子を端点へ置換した実際のテンソル（BF §2.2.7）。
方針：置換後の出力族のテンソルを元の境界次数へ移す。
規約：指定因子が辺である証明を要求する。
使われ方：辺因子の終点・始点の境界値。 -/
def endpointTensor (n : ℕ) (f : Fin n → Simplex) (k : Fin n) (hf : f k = edge)
    (b : Fin 2) : (power (interval A) n).X (-(tupleDegree n f : ℤ) + 1) :=
  tensorVectorAt A n (Function.update f k (vertex b)) (-(tupleDegree n f : ℤ) + 1)
    (by have := tupleDegree_update_edge n f k hf b; omega)

/-- 概要：先頭の辺を端点へ置換したテンソルは端点と後続のテンソル（BF §2.2.7）。
方針：先頭位置への update と反復テンソルの再帰式を使う。
規約：端点の次数は零。
使われ方：先頭因子の境界項との一致。 -/
lemma endpointTensor_zero_cons (n : ℕ) (f : Fin n → Simplex) (b : Fin 2) :
    endpointTensor A (n + 1) (Fin.cons edge f) 0 rfl b =
      ιTensorObj (interval A) (power (interval A) n) 0 (-(tupleDegree n f : ℤ))
        (-(tupleDegree (n + 1) (Fin.cons edge f) : ℤ) + 1)
        (by change (0 : ℤ) + -(tupleDegree n f : ℤ) =
              -((1 + tupleDegree n f : ℕ) : ℤ) + 1; omega)
        ((show (interval A).X 0 from faceVector A (vertex b)) ⊗ₜ[A] tensorVector A n f) := by
  unfold endpointTensor
  simp only [Fin.update_cons_zero]
  simpa only [Fin.cons_zero, Fin.cons_succ, eqToHom_refl, ModuleCat.id_apply,
    tensorVectorAt_refl] using! tensorVectorAt_succ A n (Fin.cons (vertex b) f) 0
      (-(tupleDegree n f : ℤ)) (-(tupleDegree (n + 1) (Fin.cons edge f) : ℤ) + 1)
      (by simp) rfl (by change (0 : ℤ) + -(tupleDegree n f : ℤ) =
        -((1 + tupleDegree n f : ℕ) : ℤ) + 1; omega)

/-- 概要：後続の辺を端点へ置換すると先頭因子はそのまま残る（BF §2.2.7）。
方針：後続位置の update を cons と交換し、指定次数の再帰式を使う。
規約：符号は付けず、実際のテンソル値だけを比較する。
使われ方：因子境界の再帰式と前方次数符号を分ける。 -/
lemma endpointTensor_succ_cons (n : ℕ) (s : Simplex) (f : Fin n → Simplex)
    (k : Fin n) (hf : f k = edge) (b : Fin 2) :
    endpointTensor A (n + 1) (Fin.cons s f) k.succ hf b =
      ιTensorObj (interval A) (power (interval A) n) (-(simplexDegree s : ℤ))
        (-(tupleDegree n f : ℤ) + 1)
        (-(tupleDegree (n + 1) (Fin.cons s f) : ℤ) + 1)
        (by change -(simplexDegree s : ℤ) + (-(tupleDegree n f : ℤ) + 1) =
              -((simplexDegree s + tupleDegree n f : ℕ) : ℤ) + 1
            omega)
        (faceVector A s ⊗ₜ[A] endpointTensor A n f k hf b) := by
  unfold endpointTensor
  simp only [← Fin.cons_update]
  simpa only [Fin.cons_zero, Fin.cons_succ, eqToHom_refl, ModuleCat.id_apply]
    using! tensorVectorAt_succ A n (Fin.cons s (Function.update f k (vertex b)))
      (-(simplexDegree s : ℤ)) (-(tupleDegree n f : ℤ) + 1)
      (-(tupleDegree (n + 1) (Fin.cons s f) : ℤ) + 1) rfl
      (by
        change -(tupleDegree n (Function.update f k (vertex b)) : ℤ) =
          -(tupleDegree n f : ℤ) + 1
        have := tupleDegree_update_edge n f k hf b
        omega)
      (by change -(simplexDegree s : ℤ) + (-(tupleDegree n f : ℤ) + 1) =
            -((simplexDegree s + tupleDegree n f : ℕ) : ℤ) + 1
          omega)

end SerrePositivity.EInfinity.IntervalCuts
