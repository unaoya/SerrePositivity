module

public import SerrePositivity.EInfinity.IntervalCuts.CochainInsertionDegrees
public import SerrePositivity.EInfinity.IntervalCuts.VertexFaceCuts

/-!
# 一定頂点テンソルへの実際の内側余代入

概要：Berger–Fresse §2.2.6・§3.1 の内側余作用を一定頂点族へ代入した値を計算する。
方針：面切断和を正次数では空和、次数零では一定族の一項へ戻す。
規約：内側 arity 零も含む全 arity。
使われ方：元の頂点入力における二段作用の評価。
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

/-- 概要：正次数の内側語の一定頂点族への余代入は零（BF §2.2.6・§3.1）。
方針：内側の非零面切断型が空であることを実際の余代入の有限和へ使う。
規約：両頂点と全 arity。
使われ方：二段頂点作用の正の内側次数分岐。 -/
lemma tensorCoInsertionAction_basis_vertex_zero {m n e : ℕ} (v : BasisWord n e)
    (he : 0 < e) (i : Fin (m + 1)) (b : Fin 2) :
    (tensorCoInsertionAction (interval A) (complex A n) m n i (cochainAction A n)).f (-(e : ℤ))
      (ιTensorObj (complex A n) (power (interval A) (m + 1)) (-(e : ℤ)) 0 (-(e : ℤ))
        (by omega) ((complexXIso A n e).inv (basis A n e (ULift.up v)) ⊗ₜ[A]
          tensorVectorAt A (m + 1) (fun _ => vertex b) 0 (by rw [vertex_tupleDegree]; rfl))) =
      0 := by
  let : IsEmpty (FaceCut v (vertex b)) :=
    FaceCut.isEmpty_of_nonedge_of_degree_ne_zero v (vertex b) (vertex_not_edge b) (by omega)
  have H := tensorCoInsertionAction_cochain_basis_sum_at A v i (fun _ => vertex b) 0
    (-(e : ℤ)) (by rw [vertex_tupleDegree]; rfl) (by omega)
  rw [Fintype.sum_empty, smul_zero] at H
  exact H

/-- 概要：次数零の内側語の一定頂点族への余代入は同じ頂点族（BF §2.2.6・§3.1）。
方針：唯一の面切断の係数一と一定出力を評価する。
規約：内側 arity 零でも出力の空ブロックを許す。
使われ方：二段頂点作用の内外次数零分岐。 -/
lemma tensorCoInsertionAction_basis_vertex_zero_degree {m n : ℕ} (v : BasisWord n 0)
    (i : Fin (m + 1)) (b : Fin 2) :
    (tensorCoInsertionAction (interval A) (complex A n) m n i (cochainAction A n)).f 0
      (ιTensorObj (complex A n) (power (interval A) (m + 1)) 0 0 0 rfl
        ((complexXIso A n 0).inv (basis A n 0 (ULift.up v)) ⊗ₜ[A]
          tensorVectorAt A (m + 1) (fun _ => vertex b) 0 (by rw [vertex_tupleDegree]; rfl))) =
      tensorVectorAt A (m + n) (fun _ => vertex b) 0 (by rw [vertex_tupleDegree]; rfl) := by
  have H := tensorCoInsertionAction_cochain_basis_sum_at A v i (fun _ => vertex b) 0 0
    (by rw [vertex_tupleDegree]; rfl) rfl
  simp only [Nat.cast_zero, neg_zero, zero_mul, Int.negOnePow_zero, one_smul] at H
  have hs (a : FaceCut v (vertex b)) :
      a.coefficient • tensorVectorAt A (m + n)
        (insertionFamily (fun _ : Fin (m + 1) => vertex b) a.output i) 0 (by
          rw [tupleDegree_insertionFamily]
          have := a.output_tupleDegree
          have := tupleDegree_family_blocks (fun _ : Fin (m + 1) => vertex b) i
          rw [vertex_tupleDegree, simplexDegree_vertex] at *
          omega) =
      tensorVectorAt A (m + n) (fun _ => vertex b) 0 (by rw [vertex_tupleDegree]; rfl) := by
    rw [a.coefficient_of_nonedge (vertex_not_edge b), one_smul]
    apply tensorVectorAt_congr A
    rw [a.output_of_nonedge (vertex_not_edge b), insertionFamily_const]
  have Hs := Finset.sum_congr rfl (fun a (_ha : a ∈ Finset.univ) => hs a)
  rw [Hs, Finset.sum_const, Finset.card_univ, FaceCut.card_vertex, one_smul] at H
  exact H

end SerrePositivity.EInfinity.IntervalCuts
