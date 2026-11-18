module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.FaceCutSums

/-!
模型。文献の定義との比較は後で
# 実際の複体余演算の全入力面の共通切断和

概要：Berger–Fresse §2.2.6 の cochainAction の基底語と面入力での値を共通有限和へ戻す。
方針：既存の辺・頂点の複体成分評価を使い、全三面を同じ和と指定整数次数へそろえる。
規約：任意の可換環、全 arity・語次数・入力面。
使われ方：実際の内側余演算を余代入の有限和評価へ渡す。
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

/-- 概要：実際の複体余演算の頂点入力は共通面切断和（BF §2.2.6）。
方針：語基底の次数比較の往復と頂点成分の基底値を評価する。
規約：内側語の正次数では和は空。
使われ方：二段作用の頂点入力の一項・零項を同じ添字で扱う。 -/
lemma cochainAction_basis_vertex_cut_sum {n e : ℕ} (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e) (b : Fin 2) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cochainAction A n).f (-(e : ℤ))
      (ιTensorObj (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A n) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) (-(e : ℤ)) 0 (-(e : ℤ)) (by omega)
        ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexXIso A n e).inv (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A n e (ULift.up v)) ⊗ₜ[A]
          (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.intervalXIso A 0).inv (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexChain A b))) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceCutSum A v (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex b) (-(e : ℤ)) (by rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.simplexDegree_vertex]; omega) := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceCutSum_vertex]
  simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexInputBilinear_vertex, ModuleCat.hom_inv_apply, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexComponent_basis] using!
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cochainAction_neg_vertex A n e ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexXIso A n e).inv (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A n e (ULift.up v)))
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.intervalXIso A 0).inv (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexChain A b))

/-- 概要：実際の複体余演算の辺入力は共通面切断和（BF §2.2.6）。
方針：語基底の次数比較の往復と辺成分の基底値を評価する。
規約：全ての非零辺切断を同時に含む。
使われ方：二段作用の内側辺切断の和を実際の複体射へ接続する。 -/
lemma cochainAction_basis_edge_cut_sum {n e : ℕ} (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cochainAction A n).f (-((e + 1 : ℕ) : ℤ))
      (ιTensorObj (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A n) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) (-(e : ℤ)) (-1) (-((e + 1 : ℕ) : ℤ))
        (by omega) ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexXIso A n e).inv (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A n e (ULift.up v)) ⊗ₜ[A]
          (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.intervalXIso A 1).inv (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeChain A))) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceCutSum A v _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edge (-((e + 1 : ℕ) : ℤ)) (by rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.simplexDegree_edge]; omega) := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceCutSum_edge]
  simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeInputBilinear_edge, ModuleCat.hom_inv_apply, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeComponent_basis] using!
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cochainAction_neg_edge A n e ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexXIso A n e).inv (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A n e (ULift.up v)))
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.intervalXIso A 1).inv (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeChain A))

/-- 概要：実際の複体余演算の任意の面入力は共通面切断和（BF §2.2.6）。
方針：三面の分類で辺・頂点の評価へ戻し、同じ指定整数次数で読む。
規約：出力次数は入力二次数の和を満たす任意の整数表示。
使われ方：余代入の有限和評価の内側作用の実際の入力。 -/
lemma cochainAction_basis_face_cut_sum {n e : ℕ} (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e) (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.Simplex)
    (p : ℤ) (hp : -(e : ℤ) + -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.simplexDegree s : ℤ) = p) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cochainAction A n).f p
      (ιTensorObj (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A n) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) (-(e : ℤ)) (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.simplexDegree s : ℤ)) p hp
        ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexXIso A n e).inv (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A n e (ULift.up v)) ⊗ₜ[A] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceVector A s)) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceCutSum A v s p hp := by
  rcases _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.simplex_cases s with rfl | rfl | rfl
  · have hp' : p = -(e : ℤ) := by rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.simplexDegree_vertex] at hp; omega
    cases hp'
    simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceVector, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceChain_vertex, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.simplexDegree_vertex, Nat.cast_zero, neg_zero]
      using! _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cochainAction_basis_vertex_cut_sum A v 0
  · have hp' : p = -(e : ℤ) := by rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.simplexDegree_vertex] at hp; omega
    cases hp'
    simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceVector, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceChain_vertex, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.simplexDegree_vertex, Nat.cast_zero, neg_zero]
      using! _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cochainAction_basis_vertex_cut_sum A v 1
  · have hp' : p = -((e + 1 : ℕ) : ℤ) := by rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.simplexDegree_edge] at hp; omega
    cases hp'
    simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceVector, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceChain_edge, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.simplexDegree_edge, Nat.cast_one]
      using! _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cochainAction_basis_edge_cut_sum A v

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
