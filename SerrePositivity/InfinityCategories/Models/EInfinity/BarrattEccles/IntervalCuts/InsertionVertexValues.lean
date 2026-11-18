module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.CochainInsertionDegrees
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.VertexFaceCuts

/-!
模型。文献の定義との比較は後で
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

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers

variable (A : Type u) [CommRing A]

/-- 概要：正次数の内側語の一定頂点族への余代入は零（BF §2.2.6・§3.1）。
方針：内側の非零面切断型が空であることを実際の余代入の有限和へ使う。
規約：両頂点と全 arity。
使われ方：二段頂点作用の正の内側次数分岐。 -/
lemma tensorCoInsertionAction_basis_vertex_zero {m n e : ℕ} (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e)
    (he : 0 < e) (i : Fin (m + 1)) (b : Fin 2) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorCoInsertionAction (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A n) m n i (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cochainAction A n)).f (-(e : ℤ))
      (ιTensorObj (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A n) (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) (m + 1)) (-(e : ℤ)) 0 (-(e : ℤ))
        (by omega) ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexXIso A n e).inv (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A n e (ULift.up v)) ⊗ₜ[A]
          _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVectorAt A (m + 1) (fun _ => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex b) 0 (by rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex_tupleDegree]; rfl))) =
      0 := by
  let : IsEmpty (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.FaceCut v (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex b)) :=
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.FaceCut.isEmpty_of_nonedge_of_degree_ne_zero v (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex b) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex_not_edge b) (by omega)
  have H := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorCoInsertionAction_cochain_basis_sum_at A v i (fun _ => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex b) 0
    (-(e : ℤ)) (by rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex_tupleDegree]; rfl) (by omega)
  rw [Fintype.sum_empty, smul_zero] at H
  exact H

/-- 概要：次数零の内側語の一定頂点族への余代入は同じ頂点族（BF §2.2.6・§3.1）。
方針：唯一の面切断の係数一と一定出力を評価する。
規約：内側 arity 零でも出力の空ブロックを許す。
使われ方：二段頂点作用の内外次数零分岐。 -/
lemma tensorCoInsertionAction_basis_vertex_zero_degree {m n : ℕ} (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n 0)
    (i : Fin (m + 1)) (b : Fin 2) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorCoInsertionAction (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A n) m n i (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cochainAction A n)).f 0
      (ιTensorObj (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A n) (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) (m + 1)) 0 0 0 rfl
        ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexXIso A n 0).inv (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A n 0 (ULift.up v)) ⊗ₜ[A]
          _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVectorAt A (m + 1) (fun _ => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex b) 0 (by rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex_tupleDegree]; rfl))) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVectorAt A (m + n) (fun _ => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex b) 0 (by rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex_tupleDegree]; rfl) := by
  have H := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorCoInsertionAction_cochain_basis_sum_at A v i (fun _ => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex b) 0 0
    (by rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex_tupleDegree]; rfl) rfl
  simp only [Nat.cast_zero, neg_zero, zero_mul, Int.negOnePow_zero, one_smul] at H
  have hs (a : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.FaceCut v (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex b)) :
      a.coefficient • _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVectorAt A (m + n)
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.insertionFamily (fun _ : Fin (m + 1) => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex b) a.output i) 0 (by
          rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree_insertionFamily]
          have := a.output_tupleDegree
          have := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree_family_blocks (fun _ : Fin (m + 1) => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex b) i
          rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex_tupleDegree, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.simplexDegree_vertex] at *
          omega) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVectorAt A (m + n) (fun _ => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex b) 0 (by rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex_tupleDegree]; rfl) := by
    rw [a.coefficient_of_nonedge (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex_not_edge b), one_smul]
    apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVectorAt_congr A
    rw [a.output_of_nonedge (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex_not_edge b), _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.insertionFamily_const]
  have Hs := Finset.sum_congr rfl (fun a (_ha : a ∈ Finset.univ) => hs a)
  rw [Hs, Finset.sum_const, Finset.card_univ, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.FaceCut.card_vertex, one_smul] at H
  exact H

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
