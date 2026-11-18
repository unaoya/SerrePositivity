module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.TensorDegreeTransport
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.TupleUpdates

/-!
模型。文献の定義との比較は後で
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

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers

variable (A : Type u) [CommRing A]

/-- 概要：指定した辺因子を端点へ置換した実際のテンソル（BF §2.2.7）。
方針：置換後の出力族のテンソルを元の境界次数へ移す。
規約：指定因子が辺である証明を要求する。
使われ方：辺因子の終点・始点の境界値。 -/
def endpointTensor (n : ℕ) (f : Fin n → _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.Simplex) (k : Fin n) (hf : f k = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edge)
    (b : Fin 2) : (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) n).X (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree n f : ℤ) + 1) :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVectorAt A n (Function.update f k (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex b)) (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree n f : ℤ) + 1)
    (by have := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree_update_edge n f k hf b; omega)

/-- 概要：先頭の辺を端点へ置換したテンソルは端点と後続のテンソル（BF §2.2.7）。
方針：先頭位置への update と反復テンソルの再帰式を使う。
規約：端点の次数は零。
使われ方：先頭因子の境界項との一致。 -/
lemma endpointTensor_zero_cons (n : ℕ) (f : Fin n → _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.Simplex) (b : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.endpointTensor A (n + 1) (Fin.cons _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edge f) 0 rfl b =
      ιTensorObj (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) n) 0 (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree n f : ℤ))
        (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree (n + 1) (Fin.cons _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edge f) : ℤ) + 1)
        (by change (0 : ℤ) + -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree n f : ℤ) =
              -((1 + _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree n f : ℕ) : ℤ) + 1; omega)
        ((show (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A).X 0 from _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceVector A (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex b)) ⊗ₜ[A] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVector A n f) := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.endpointTensor
  simp only [Fin.update_cons_zero]
  simpa only [Fin.cons_zero, Fin.cons_succ, eqToHom_refl, ModuleCat.id_apply,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVectorAt_refl] using! _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVectorAt_succ A n (Fin.cons (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex b) f) 0
      (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree n f : ℤ)) (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree (n + 1) (Fin.cons _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edge f) : ℤ) + 1)
      (by simp) rfl (by change (0 : ℤ) + -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree n f : ℤ) =
        -((1 + _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree n f : ℕ) : ℤ) + 1; omega)

/-- 概要：後続の辺を端点へ置換すると先頭因子はそのまま残る（BF §2.2.7）。
方針：後続位置の update を cons と交換し、指定次数の再帰式を使う。
規約：符号は付けず、実際のテンソル値だけを比較する。
使われ方：因子境界の再帰式と前方次数符号を分ける。 -/
lemma endpointTensor_succ_cons (n : ℕ) (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.Simplex) (f : Fin n → _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.Simplex)
    (k : Fin n) (hf : f k = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edge) (b : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.endpointTensor A (n + 1) (Fin.cons s f) k.succ hf b =
      ιTensorObj (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) n) (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.simplexDegree s : ℤ))
        (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree n f : ℤ) + 1)
        (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree (n + 1) (Fin.cons s f) : ℤ) + 1)
        (by change -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.simplexDegree s : ℤ) + (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree n f : ℤ) + 1) =
              -((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.simplexDegree s + _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree n f : ℕ) : ℤ) + 1
            omega)
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceVector A s ⊗ₜ[A] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.endpointTensor A n f k hf b) := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.endpointTensor
  simp only [← Fin.cons_update]
  simpa only [Fin.cons_zero, Fin.cons_succ, eqToHom_refl, ModuleCat.id_apply]
    using! _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVectorAt_succ A n (Fin.cons s (Function.update f k (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex b)))
      (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.simplexDegree s : ℤ)) (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree n f : ℤ) + 1)
      (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree (n + 1) (Fin.cons s f) : ℤ) + 1) rfl
      (by
        change -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree n (Function.update f k (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex b)) : ℤ) =
          -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree n f : ℤ) + 1
        have := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree_update_edge n f k hf b
        omega)
      (by change -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.simplexDegree s : ℤ) + (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree n f : ℤ) + 1) =
            -((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.simplexDegree s + _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree n f : ℕ) : ℤ) + 1
          omega)

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
