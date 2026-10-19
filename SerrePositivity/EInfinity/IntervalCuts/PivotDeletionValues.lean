module

public import SerrePositivity.EInfinity.IntervalCuts.PivotDeletionSigns
public import SerrePositivity.EInfinity.IntervalCuts.PivotDeletionOutputs

/-!
# 切断点障害の実際の符号付き削除値

概要：Berger–Fresse §2.2.7 の実際の削除係数付き区間テンソルを隙間値へ移す。
方針：一般係数公式と出力テンソルの一致を組み合わせる。
規約：左削除は共通係数の負、右削除は正の隙間値。
使われ方：隣接切断が両方退化する隙間での二削除項の相殺と全有限和の比較。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.IntervalCuts

open Surjection

/-- 概要：左の切断点障害の実際の符号付き削除値は共通係数の負の隙間値（BF §2.2.7）。
方針：係数と実際のテンソルの公式を代入する。
規約：語の次数 d+1 と出力次数 d+1 を保つ。
使われ方：全削除和の左の切断点障害部分。 -/
lemma pivotDeletion_weighted_before (A : Type u) [CommRing A] {n d : ℕ}
    (u : BasisWord n (d + 1)) (i : Fin (n + (d + 1))) (q : Fin (n + d))
    (h : EdgeNondegenerate (erase u.val i) q) (hu : u.val i = u.val (i.succAbove q))
    (hi : i < i.succAbove q) :
    (deletionCoefficient u.val i * edgeSign (erase u.val i) q) •
        tensorVectorOfDegree A n (d + 1) (edgeOutput (pivotEraseBasisWord u i q h hu) q)
          (edgeOutput_tupleDegree _ _ h) =
      -(((-1 : ℤ) ^ (Finset.univ.filter (Caesura u.val)).card *
          (-1 : ℤ) ^ positionInversionCount u.val (Finset.univ.filter (Caesura u.val))) •
        gapTensor A u (i.succAbove q).castSucc) := by
  rw [pivotDeletion_coefficient_before u.val i q h hi hu,
    pivotErase_tensor_before A u i q h hu hi, neg_smul]

/-- 概要：右の切断点障害の実際の符号付き削除値は共通係数の隙間値（BF §2.2.7）。
方針：係数と実際のテンソルの公式を代入する。
規約：語の次数 d+1 と出力次数 d+1 を保つ。
使われ方：全削除和の右の切断点障害部分。 -/
lemma pivotDeletion_weighted_after (A : Type u) [CommRing A] {n d : ℕ}
    (u : BasisWord n (d + 1)) (i : Fin (n + (d + 1))) (q : Fin (n + d))
    (h : EdgeNondegenerate (erase u.val i) q) (hu : u.val i = u.val (i.succAbove q))
    (hi : i.succAbove q < i) :
    (deletionCoefficient u.val i * edgeSign (erase u.val i) q) •
        tensorVectorOfDegree A n (d + 1) (edgeOutput (pivotEraseBasisWord u i q h hu) q)
          (edgeOutput_tupleDegree _ _ h) =
      ((-1 : ℤ) ^ (Finset.univ.filter (Caesura u.val)).card *
          (-1 : ℤ) ^ positionInversionCount u.val (Finset.univ.filter (Caesura u.val))) •
        gapTensor A u (i.succAbove q).succ := by
  rw [pivotDeletion_coefficient_after u.val i q h hi hu,
    pivotErase_tensor_after A u i q h hu hi]

/-- 概要：同じ隙間へ戻る左右二つの実際の切断点障害削除値は相殺（BF §2.2.7）。
方針：同じ共通係数の負・正の隙間値へ移して加える。
規約：元の非零辺切断の存在も係数環の標数条件も要求しない。
使われ方：隙間の両隣が退化する場合を全有限和から消す。 -/
lemma pivotDeletion_weighted_pair (A : Type u) [CommRing A] {n d : ℕ}
    (u : BasisWord n (d + 1)) (i j : Fin (n + (d + 1))) (q r : Fin (n + d))
    (h : EdgeNondegenerate (erase u.val i) q) (h' : EdgeNondegenerate (erase u.val j) r)
    (hu : u.val i = u.val (i.succAbove q)) (hu' : u.val j = u.val (j.succAbove r))
    (hi : i < i.succAbove q) (hj : j.succAbove r < j)
    (hgap : (i.succAbove q).castSucc = (j.succAbove r).succ) :
    (deletionCoefficient u.val i * edgeSign (erase u.val i) q) •
        tensorVectorOfDegree A n (d + 1) (edgeOutput (pivotEraseBasisWord u i q h hu) q)
          (edgeOutput_tupleDegree _ _ h) +
      (deletionCoefficient u.val j * edgeSign (erase u.val j) r) •
        tensorVectorOfDegree A n (d + 1) (edgeOutput (pivotEraseBasisWord u j r h' hu') r)
          (edgeOutput_tupleDegree _ _ h') = 0 := by
  rw [pivotDeletion_weighted_before A u i q h hu hi,
    pivotDeletion_weighted_after A u j r h' hu' hj, hgap, neg_add_cancel]

end SerrePositivity.EInfinity.IntervalCuts
