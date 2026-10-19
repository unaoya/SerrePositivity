module

public import SerrePositivity.EInfinity.IntervalCuts.FaceCutSums

/-!
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

namespace SerrePositivity.EInfinity.IntervalCuts

open CategoryTheory MonoidalCategory HomologicalComplex Surjection
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers

variable (A : Type u) [CommRing A]

/-- 概要：実際の複体余演算の頂点入力は共通面切断和（BF §2.2.6）。
方針：語基底の次数比較の往復と頂点成分の基底値を評価する。
規約：内側語の正次数では和は空。
使われ方：二段作用の頂点入力の一項・零項を同じ添字で扱う。 -/
lemma cochainAction_basis_vertex_cut_sum {n e : ℕ} (v : BasisWord n e) (b : Fin 2) :
    (cochainAction A n).f (-(e : ℤ))
      (ιTensorObj (complex A n) (interval A) (-(e : ℤ)) 0 (-(e : ℤ)) (by omega)
        ((complexXIso A n e).inv (basis A n e (ULift.up v)) ⊗ₜ[A]
          (intervalXIso A 0).inv (vertexChain A b))) =
      faceCutSum A v (vertex b) (-(e : ℤ)) (by rw [simplexDegree_vertex]; omega) := by
  rw [faceCutSum_vertex]
  simpa only [vertexInputBilinear_vertex, ModuleCat.hom_inv_apply, vertexComponent_basis] using!
    cochainAction_neg_vertex A n e ((complexXIso A n e).inv (basis A n e (ULift.up v)))
      ((intervalXIso A 0).inv (vertexChain A b))

/-- 概要：実際の複体余演算の辺入力は共通面切断和（BF §2.2.6）。
方針：語基底の次数比較の往復と辺成分の基底値を評価する。
規約：全ての非零辺切断を同時に含む。
使われ方：二段作用の内側辺切断の和を実際の複体射へ接続する。 -/
lemma cochainAction_basis_edge_cut_sum {n e : ℕ} (v : BasisWord n e) :
    (cochainAction A n).f (-((e + 1 : ℕ) : ℤ))
      (ιTensorObj (complex A n) (interval A) (-(e : ℤ)) (-1) (-((e + 1 : ℕ) : ℤ))
        (by omega) ((complexXIso A n e).inv (basis A n e (ULift.up v)) ⊗ₜ[A]
          (intervalXIso A 1).inv (edgeChain A))) =
      faceCutSum A v edge (-((e + 1 : ℕ) : ℤ)) (by rw [simplexDegree_edge]; omega) := by
  rw [faceCutSum_edge]
  simpa only [edgeInputBilinear_edge, ModuleCat.hom_inv_apply, edgeComponent_basis] using!
    cochainAction_neg_edge A n e ((complexXIso A n e).inv (basis A n e (ULift.up v)))
      ((intervalXIso A 1).inv (edgeChain A))

/-- 概要：実際の複体余演算の任意の面入力は共通面切断和（BF §2.2.6）。
方針：三面の分類で辺・頂点の評価へ戻し、同じ指定整数次数で読む。
規約：出力次数は入力二次数の和を満たす任意の整数表示。
使われ方：余代入の有限和評価の内側作用の実際の入力。 -/
lemma cochainAction_basis_face_cut_sum {n e : ℕ} (v : BasisWord n e) (s : Simplex)
    (p : ℤ) (hp : -(e : ℤ) + -(simplexDegree s : ℤ) = p) :
    (cochainAction A n).f p
      (ιTensorObj (complex A n) (interval A) (-(e : ℤ)) (-(simplexDegree s : ℤ)) p hp
        ((complexXIso A n e).inv (basis A n e (ULift.up v)) ⊗ₜ[A] faceVector A s)) =
      faceCutSum A v s p hp := by
  rcases simplex_cases s with rfl | rfl | rfl
  · have hp' : p = -(e : ℤ) := by rw [simplexDegree_vertex] at hp; omega
    cases hp'
    simpa only [faceVector, faceChain_vertex, simplexDegree_vertex, Nat.cast_zero, neg_zero]
      using! cochainAction_basis_vertex_cut_sum A v 0
  · have hp' : p = -(e : ℤ) := by rw [simplexDegree_vertex] at hp; omega
    cases hp'
    simpa only [faceVector, faceChain_vertex, simplexDegree_vertex, Nat.cast_zero, neg_zero]
      using! cochainAction_basis_vertex_cut_sum A v 1
  · have hp' : p = -((e + 1 : ℕ) : ℤ) := by rw [simplexDegree_edge] at hp; omega
    cases hp'
    simpa only [faceVector, faceChain_edge, simplexDegree_edge, Nat.cast_one]
      using! cochainAction_basis_edge_cut_sum A v

end SerrePositivity.EInfinity.IntervalCuts
