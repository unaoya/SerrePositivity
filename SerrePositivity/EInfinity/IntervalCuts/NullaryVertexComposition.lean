module

public import SerrePositivity.EInfinity.IntervalCuts.CompositionVertexGenerators
public import SerrePositivity.EInfinity.IntervalCuts.TripleGeneratorExt

/-!
# 空語を含む全 arity の頂点部分合成則

概要：Berger–Fresse §2.2.6・§3.1 の両頂点での合成則を nullary まで拡張する。
方針：次数零の合成語の全射性を用い、正次数では既存の頂点零性を適用する。
規約：内側 arity 零、出力 arity 零、全内外語次数を含む。
使われ方：χ-coalgebra の全整数複体射の部分合成則の頂点入力。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.IntervalCuts

open CategoryTheory MonoidalCategory HomologicalComplex Surjection
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers

variable (A : Type u) [CommRing A]

/-- 概要：次数零の正規化合成項の頂点値は一定頂点テンソル（BF §2.2.6）。
方針：合成語の長さと全射性を使い、同濃度の全射生成元の公式へ戻す。
規約：空の内側語と空の出力語も含む。
使われ方：nullary の次数零の合成頂点値。 -/
lemma vertexComponent_compositeGenerator_zero {m n : ℕ} (u : BasisWord (m + 1) 0)
    (v : BasisWord n 0) (i : Fin (m + 1))
    (r : OverlapPartition (occurrenceCount u.val i) (n + 0)) (b : Fin 2) :
    vertexComponent A (m + n) 0 b (compositeGenerator A u v i r) =
      tensorVectorAt A (m + n) (fun _ => vertex b) 0 (by rw [vertex_tupleDegree]; rfl) := by
  unfold compositeGenerator listGenerator
  rw [dite_eq_left (compositeWord_length u v i r)]
  apply vertexComponent_generator_zero_degree A _ ?_ b
  intro a
  obtain ⟨j, hj⟩ := compositeWord_surjective u v i r a
  exact ⟨Fin.cast (compositeWord_length u v i r) j, hj⟩

/-- 概要：全 arity の次数零合成の頂点値は一定頂点テンソル（BF §2.2.6）。
方針：外側の各色は一出現なので唯一分割の正符号の一項を評価する。
規約：内側・出力 arity 零も含む。
使われ方：元の頂点での実際の合成則の次数零分岐。 -/
lemma vertexComponent_composition_zero_all {m n : ℕ} (u : BasisWord (m + 1) 0)
    (v : BasisWord n 0) (i : Fin (m + 1)) (b : Fin 2) :
    vertexComponent A (m + n) 0 b (compositionOnWords A u v i) =
      tensorVectorAt A (m + n) (fun _ => vertex b) 0 (by rw [vertex_tupleDegree]; rfl) := by
  have hc := overlapPartition_card_of_count_one (l := n + 0) (occurrenceCount_degree_zero u i)
  unfold compositionOnWords
  simp only [map_sum, compositionSign_inner_degree_zero, one_smul,
    vertexComponent_compositeGenerator_zero A u v i _ b, Finset.sum_const,
    Finset.card_univ, hc, one_smul]

/-- 概要：両頂点における実際の部分合成則は全 arity で成立（BF §2.2.6・§3.1）。
方針：内外語次数零では一定頂点、正次数では左右の零性を連結する。
規約：nullary と出力 arity 零を含み、全語次数。
使われ方：全複体射の合成則を三生成元外延性で閉じる頂点条件。 -/
lemma cochainAction_composition_basis_vertex_eq_iterated_all {m n d e : ℕ}
    (u : BasisWord (m + 1) d) (v : BasisWord n e) (i : Fin (m + 1)) (b : Fin 2) :
    ((complexPartialComposition A m n i ▷ interval A) ≫ cochainAction A (m + n)).f
      (-((d + e : ℕ) : ℤ)) (wordPairVertexInput A u v b) =
        (iteratedCochainAction A m n i).f (-((d + e : ℕ) : ℤ))
          (wordPairVertexInput A u v b) := by
  refine (cochainAction_composition_basis_vertex A u v i b).trans ?_
  by_cases hd : d = 0
  · subst d
    by_cases he : e = 0
    · subst e
      exact (vertexComponent_composition_zero_all A u v i b).trans
        (iteratedCochainAction_basis_vertex_zero A u v i b).symm
    · have hL : vertexComponent A (m + n) (0 + e) b (compositionOnWords A u v i) = 0 := by
        rw [vertexComponent_eq_zero_of_positive A (m + n) (0 + e) b (by omega),
          LinearMap.zero_apply]
      exact hL.trans (iteratedCochainAction_basis_vertex_inner_positive A u v i b (by omega)
        (-((0 + e : ℕ) : ℤ)) (by omega)).symm
  · have hL : vertexComponent A (m + n) (d + e) b (compositionOnWords A u v i) = 0 := by
      rw [vertexComponent_eq_zero_of_positive A (m + n) (d + e) b (by omega),
        LinearMap.zero_apply]
    exact hL.trans (iteratedCochainAction_basis_vertex_outer_positive A u v i b (by omega)).symm

end SerrePositivity.EInfinity.IntervalCuts
