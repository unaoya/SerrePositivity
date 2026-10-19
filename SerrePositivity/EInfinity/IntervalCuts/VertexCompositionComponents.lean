module

public import SerrePositivity.EInfinity.IntervalCuts.Components
public import SerrePositivity.EInfinity.Surjection.CompositeBasis
public import SerrePositivity.EInfinity.Surjection.CompositionBoundaryCases
public import SerrePositivity.EInfinity.IntervalCuts.SingleSlotPositions

/-!
# 合成語の頂点成分

概要：Berger–Fresse §2.2.6 の合成語加群に対する頂点成分を計算する。
方針：正次数では全基底を零へ送り、次数零では唯一の合成分割を使う。
規約：次数零の合成計算は正の内側 arity で行う。
使われ方：実際の部分合成則の元の頂点入力における左辺。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.EInfinity.IntervalCuts

open Surjection
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers

variable (A : Type u) [CommRing A]

/-- 概要：次数零の外側語の各色は一出現（BF §1.2.1）。
方針：有限自己全射の単射性から語リストの Nodup と色の所属を使う。
規約：指定色が存在する arity。
使われ方：合成の分割型が一部分割となること。 -/
lemma occurrenceCount_degree_zero {n : ℕ} (u : BasisWord n 0) (k : Fin n) :
    occurrenceCount u.val k = 1 := by
  apply List.count_eq_one_of_mem
  · exact List.nodup_ofFn_ofInjective (Finite.injective_iff_surjective.mpr u.surjective)
  · obtain ⟨j, hj⟩ := u.surjective k
    exact List.mem_ofFn.mpr ⟨j, hj⟩

/-- 概要：部分数一の重なる分割の有限型は一元（BF §1.2.4）。
方針：全ての一部分割を既存の single に同定する。
規約：空語長も含む。
使われ方：次数零の合成頂点成分の有限和を一項にする。 -/
lemma overlapPartition_card_of_count_one {t l : ℕ} (ht : t = 1) :
    Fintype.card (OverlapPartition t l) = 1 := by
  subst t
  exact Fintype.card_eq_one_iff.mpr ⟨OverlapPartition.single l, fun r => r.eq_single⟩

/-- 概要：次数零の二語の合成の頂点成分は一定頂点テンソル（BF §2.2.6）。
方針：唯一の合成分割の基底値と正の合成符号を評価する。
規約：正の内側 arity、両頂点。
使われ方：実際の部分合成則の頂点入力の次数零分岐。 -/
lemma vertexComponent_composition_zero {m n : ℕ} (u : BasisWord (m + 1) 0)
    (v : BasisWord n 0) (i : Fin (m + 1)) (hn : 0 < n) (b : Fin 2) :
    vertexComponent A (m + n) 0 b (compositionOnWords A u v i) =
      tensorVectorAt A (m + n) (fun _ => vertex b) 0 (by rw [vertex_tupleDegree]; rfl) := by
  have hc := overlapPartition_card_of_count_one (l := n + 0) (occurrenceCount_degree_zero u i)
  unfold compositionOnWords
  simp only [map_sum, compositionSign_inner_degree_zero, one_smul,
    compositeGenerator_eq_basis A u v i _ hn, vertexComponent_basis, vertexComponentOnWord,
    Finset.sum_const, Finset.card_univ, hc, one_smul]
  rfl

end SerrePositivity.EInfinity.IntervalCuts
