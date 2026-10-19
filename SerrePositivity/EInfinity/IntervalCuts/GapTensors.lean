module

public import SerrePositivity.EInfinity.IntervalCuts.GapOutputs
public import SerrePositivity.EInfinity.IntervalCuts.FactorBoundary
public import SerrePositivity.EInfinity.IntervalCuts.PivotBoundarySigns

/-!
# 隙間切断の実際の区間テンソル

概要：Berger–Fresse §2.2.7 の切断点色の因子境界を共通次数の隙間テンソルの差で表す。
方針：端点置換と隙間出力の一致で次数を下げ、切断点に依存しない係数を取り出す。
規約：実際の非有界整数複体の次数 −d を使い、次数の異なる隙間値は零とする。
使われ方：切断点色の因子境界の望遠和。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.IntervalCuts

open Surjection CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers

/-- 概要：非零切断の切断点色を端点へ置換した族の次数は語次数（BF §2.2.7）。
方針：元出力の次数 d+1 と辺置換による次数一減少を使う。
規約：両端点を同時に扱う。
使われ方：全切断の境界値を同じ −d 成分へ置く。 -/
lemma pivotEndpoint_tupleDegree {n d : ℕ} (u : BasisWord n d) (p : Fin (n + d))
    (h : EdgeNondegenerate u.val p) (b : Fin 2) :
    tupleDegree n (Function.update (edgeOutput u p) (u.val p) (vertex b)) = d := by
  have he : edgeOutput u p (u.val p) = edge :=
    (edgeOutput_eq_edge_iff u p h _).mpr ⟨p, Finset.mem_insert_self _ _, rfl⟩
  have ht := tupleDegree_update_edge n (edgeOutput u p) (u.val p) he b
  rw [edgeOutput_tupleDegree u p h] at ht
  omega

/-- 概要：非零切断直前の隙間出力の総次数は語次数（BF §2.2.7）。
方針：切断点色を終点へ置換した族に戻す。
規約：隙間は切断点を右側へ置く。
使われ方：望遠和の正側の値を次数付けする。 -/
lemma gapOutput_tupleDegree_before {n d : ℕ} (u : BasisWord n d) (p : Fin (n + d))
    (h : EdgeNondegenerate u.val p) : tupleDegree n (gapOutput u p.castSucc) = d := by
  rw [← edgeOutput_pivot_endpoint_one u p h]
  exact pivotEndpoint_tupleDegree u p h 1

/-- 概要：非零切断直後の隙間出力の総次数は語次数（BF §2.2.7）。
方針：切断点色を始点へ置換した族に戻す。
規約：隙間は切断点を左側へ置く。
使われ方：望遠和の負側の値を次数付けする。 -/
lemma gapOutput_tupleDegree_after {n d : ℕ} (u : BasisWord n d) (p : Fin (n + d))
    (h : EdgeNondegenerate u.val p) : tupleDegree n (gapOutput u p.succ) = d := by
  rw [← edgeOutput_pivot_endpoint_zero u p h]
  exact pivotEndpoint_tupleDegree u p h 0

variable (A : Type u) [CommRing A]

/-- 概要：隙間出力を語次数の実際の区間テンソルへ送る（BF §2.2.7）。
方針：総次数が語次数なら指定次数のテンソル生成元を取り、それ以外は零とする。
規約：全隙間で定義し、非零切断の前後では次数条件を証明して評価する。
使われ方：証明を添字へ加えずに隙間値の望遠和を取る。 -/
def gapTensor {n d : ℕ} (u : BasisWord n d) (q : Fin (n + d + 1)) :
    (power (interval A) n).X (-(d : ℤ)) :=
  if h : tupleDegree n (gapOutput u q) = d then
    tensorVectorOfDegree A n d (gapOutput u q) h else 0

/-- 概要：正しい総次数を持つ隙間の値は実際のテンソル生成元（BF §2.2.7）。
方針：定義の次数判定を証明で解く。
規約：次数証明の選択は値に影響しない。
使われ方：切断の両端点置換との一致。 -/
lemma gapTensor_eq {n d : ℕ} (u : BasisWord n d) (q : Fin (n + d + 1))
    (h : tupleDegree n (gapOutput u q) = d) :
    gapTensor A u q = tensorVectorOfDegree A n d (gapOutput u q) h := by
  simp only [gapTensor, dite_eq_left h]

/-- 概要：切断点色の終点置換の実際のテンソルは直前の隙間値（BF §2.2.7）。
方針：出力族の一致を同じ −d 成分へ移す。
規約：指定次数のテンソルで比較する。
使われ方：隣接切断の端点項の相殺。 -/
lemma pivotEndpoint_tensor_one {n d : ℕ} (u : BasisWord n d) (p : Fin (n + d))
    (h : EdgeNondegenerate u.val p) :
    tensorVectorOfDegree A n d (Function.update (edgeOutput u p) (u.val p) (vertex 1))
      (pivotEndpoint_tupleDegree u p h 1) = gapTensor A u p.castSucc := by
  rw [gapTensor_eq A u _ (gapOutput_tupleDegree_before u p h)]
  exact tensorVectorAt_congr A n _ _ (-(d : ℤ))
    (congrArg (fun r : ℕ => -(r : ℤ)) (pivotEndpoint_tupleDegree u p h 1))
    (congrArg (fun r : ℕ => -(r : ℤ)) (gapOutput_tupleDegree_before u p h))
    (edgeOutput_pivot_endpoint_one u p h)

/-- 概要：切断点色の始点置換の実際のテンソルは直後の隙間値（BF §2.2.7）。
方針：出力族の一致を同じ −d 成分へ移す。
規約：指定次数のテンソルで比較する。
使われ方：隣接切断の端点項の相殺。 -/
lemma pivotEndpoint_tensor_zero {n d : ℕ} (u : BasisWord n d) (p : Fin (n + d))
    (h : EdgeNondegenerate u.val p) :
    tensorVectorOfDegree A n d (Function.update (edgeOutput u p) (u.val p) (vertex 0))
      (pivotEndpoint_tupleDegree u p h 0) = gapTensor A u p.succ := by
  rw [gapTensor_eq A u _ (gapOutput_tupleDegree_after u p h)]
  exact tensorVectorAt_congr A n _ _ (-(d : ℤ))
    (congrArg (fun r : ℕ => -(r : ℤ)) (pivotEndpoint_tupleDegree u p h 0))
    (congrArg (fun r : ℕ => -(r : ℤ)) (gapOutput_tupleDegree_after u p h))
    (edgeOutput_pivot_endpoint_zero u p h)

/-- 概要：切断点色の実際の因子境界は共通係数付き隙間テンソルの差（BF §2.2.7）。
方針：端点境界公式を −d へ移し、出力族と境界係数の公式を使う。
規約：左辺は元の実際の因子境界に次数等式の射を適用したもの。
使われ方：全非零切断にわたる境界和の内部相殺。 -/
lemma pivotBoundary_gap_difference {n d : ℕ} (u : BasisWord n d) (p : Fin (n + d))
    (h : EdgeNondegenerate u.val p) :
    eqToHom (congrArg (fun r : ℤ => (power (interval A) n).X r)
        (by have := edgeOutput_tupleDegree u p h
            omega : -(tupleDegree n (edgeOutput u p) : ℤ) + 1 = -(d : ℤ)))
      (edgeSign u.val p • tensorBoundaryTerm A n (edgeOutput u p) (u.val p)) =
      ((-1 : ℤ) ^ (Finset.univ.filter (Caesura u.val)).card *
        (-1 : ℤ) ^ positionInversionCount u.val (Finset.univ.filter (Caesura u.val))) •
          (gapTensor A u p.castSucc - gapTensor A u p.succ) := by
  have he : edgeOutput u p (u.val p) = edge :=
    (edgeOutput_eq_edge_iff u p h _).mpr ⟨p, Finset.mem_insert_self _ _, rfl⟩
  rw [tensorBoundaryTerm_eq_endpoints A n _ _ he]
  simp only [map_zsmul, map_sub, smul_smul]
  have hs := edgeSign_pivot_boundary u p h
  change edgeSign u.val p * (-1 : ℤ) ^ prefixDegree n (edgeOutput u p) (u.val p) = _ at hs
  rw [hs]
  congr 1
  have ht (b : Fin 2) :
      eqToHom (congrArg (fun r : ℤ => (power (interval A) n).X r)
          (by have := edgeOutput_tupleDegree u p h
              omega : -(tupleDegree n (edgeOutput u p) : ℤ) + 1 = -(d : ℤ)))
        (endpointTensor A n (edgeOutput u p) (u.val p) he b) =
        tensorVectorOfDegree A n d (Function.update (edgeOutput u p) (u.val p) (vertex b))
          (pivotEndpoint_tupleDegree u p h b) := by
    simp only [endpointTensor, tensorVectorAt, tensorVectorOfDegree,
      ← ModuleCat.comp_apply, eqToHom_trans]
  rw [ht, ht, pivotEndpoint_tensor_one A u p h, pivotEndpoint_tensor_zero A u p h]

/-- 概要：次数零の先頭前隙間の実際の値は全因子が一頂点のテンソル（BF §2.2.7）。
方針：出力族と総次数を簡約する。
規約：arity 零も含む。
使われ方：入力辺の終点の余演算との比較。 -/
lemma gapTensor_first_zeroDegree {n : ℕ} (u : BasisWord n 0) :
    gapTensor A u 0 = tensorVectorOfDegree A n 0 (fun _ => vertex 1)
      (vertex_tupleDegree n 1) := by
  have h : tupleDegree n (gapOutput u 0) = 0 := by
    rw [gapOutput_first]
    exact vertex_tupleDegree n 1
  simpa only [gapOutput_first] using! gapTensor_eq A u 0 h

/-- 概要：次数零の末尾後隙間の実際の値は全因子が零頂点のテンソル（BF §2.2.7）。
方針：出力族と総次数を簡約する。
規約：arity 零も含む。
使われ方：入力辺の始点の余演算との比較。 -/
lemma gapTensor_last_zeroDegree {n : ℕ} (u : BasisWord n 0) :
    gapTensor A u (Fin.last n) = tensorVectorOfDegree A n 0 (fun _ => vertex 0)
      (vertex_tupleDegree n 0) := by
  have hl : gapOutput u (Fin.last n) = fun _ => vertex 0 := gapOutput_last u
  have h : tupleDegree n (gapOutput u (Fin.last n)) = 0 := by
    rw [hl]
    exact vertex_tupleDegree n 0
  simpa only [hl] using! gapTensor_eq A u (Fin.last n) h

end SerrePositivity.EInfinity.IntervalCuts
