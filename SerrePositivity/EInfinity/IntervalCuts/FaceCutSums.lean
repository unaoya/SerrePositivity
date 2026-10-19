module

public import SerrePositivity.EInfinity.IntervalCuts.FaceCuts
public import SerrePositivity.EInfinity.IntervalCuts.CochainAction

/-!
# 実際の辺・頂点余演算と共通面切断和

概要：Berger–Fresse §2.2.6 の実際の区間余演算の辺・頂点値を同じ有限和で表示する。
方針：辺切断との有限同値、次数零頂点の一項同値、正次数頂点の空和を使う。
規約：指定整数次数は語次数と面次数の負の和。
使われ方：内側 cochainAction の全値を余代入の有限和評価へ渡す。
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

/-- 概要：指定面入力の共通の符号付き面テンソル和（BF §2.2.6）。
方針：全非零面切断の係数と出力族を実際の面テンソルへ送る。
規約：指定整数次数の証明を要求する。
使われ方：辺・頂点の実際の余演算の統一した表示。 -/
def faceCutSum {n e : ℕ} (v : BasisWord n e) (s : Simplex) (p : ℤ)
    (hp : -(e : ℤ) + -(simplexDegree s : ℤ) = p) : (power (interval A) n).X p :=
  ∑ a : FaceCut v s, a.coefficient • tensorVectorAt A n a.output p
    (by rw [a.output_tupleDegree]; omega)

/-- 概要：辺入力の共通面切断和は既存の実際の辺成分（BF §2.2.6）。
方針：共通面切断の有限型を非零辺切断へ移す。
規約：元の整数切断符号を保持する。
使われ方：辺入力で統一和の値を確定する。 -/
lemma faceCutSum_edge {n e : ℕ} (v : BasisWord n e) :
    faceCutSum A v edge (-((e + 1 : ℕ) : ℤ)) (by rw [simplexDegree_edge]; omega) =
      edgeComponentOnWord A v := by
  rw [faceCutSum, edgeComponentOnWord_sum_subtype]
  exact ((FaceCut.edgeEquiv v).symm.sum_comp (fun a : FaceCut v edge =>
    a.coefficient • tensorVectorAt A n a.output (-((e + 1 : ℕ) : ℤ))
      (by rw [a.output_tupleDegree, simplexDegree_edge]))).symm

private lemma vertex_ne_edge (b : Fin 2) : vertex b ≠ edge := by
  intro he
  have h := congrArg simplexDegree he
  simp only [simplexDegree_vertex, simplexDegree_edge] at h
  exact Nat.zero_ne_one h

/-- 概要：頂点入力の共通面切断和は既存の実際の頂点成分（BF §2.2.6）。
方針：次数零は一項同値、正次数は空型として有限和を評価する。
規約：両頂点と arity 零を含む。
使われ方：頂点入力で統一和の値を確定する。 -/
lemma faceCutSum_vertex {n e : ℕ} (v : BasisWord n e) (b : Fin 2) :
    faceCutSum A v (vertex b) (-(e : ℤ)) (by rw [simplexDegree_vertex]; omega) =
      vertexComponentOnWord A v b := by
  by_cases he : e = 0
  · subst e
    rw [faceCutSum]
    have H := (FaceCut.vertexEquiv v (vertex b) (vertex_ne_edge b) rfl).symm.sum_comp
      (fun a : FaceCut v (vertex b) => a.coefficient • tensorVectorAt A n a.output 0
        (by rw [a.output_tupleDegree, simplexDegree_vertex]; rfl))
    simp only [Fintype.sum_unique, FaceCut.vertexEquiv, Equiv.coe_fn_symm_mk, FaceCut.coefficient,
      one_smul] at H
    calc
      _ = tensorVectorAt A n (fun _ => vertex b) 0 (by rw [vertex_tupleDegree]; rfl) := by
        simpa only [FaceCut.coefficient] using! H.symm
      _ = _ := by
        rw [vertexComponentOnWord, dite_eq_left rfl]
        rfl
  · let : IsEmpty (FaceCut v (vertex b)) :=
      FaceCut.isEmpty_of_nonedge_of_degree_ne_zero v (vertex b) (vertex_ne_edge b) he
    rw [faceCutSum, Fintype.sum_empty]
    exact (vertexComponentOnWord_eq_zero_of_positive A v (by omega) b).symm

end SerrePositivity.EInfinity.IntervalCuts
