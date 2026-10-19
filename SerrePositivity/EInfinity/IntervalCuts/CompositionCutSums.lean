module

public import SerrePositivity.EInfinity.IntervalCuts.CochainPermutation
public import SerrePositivity.EInfinity.Surjection.CompositeBasis
public import SerrePositivity.EInfinity.Surjection.ComplexComposition

/-!
# 部分合成後の実際の辺成分の二重切断和

概要：Berger–Fresse §2.2.6 の合成係数の作用を、重なる分割と合成語の辺切断の和へ展開する。
方針：部分合成の有限和を線形性で外へ出し、正の内側 arity では実際の合成基底語を使う。
規約：正規化と符号を構成済みの合成・切断のものに固定する。
使われ方：二段切断との有限添字対応で部分合成則の左辺を比較する。
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

/-- 概要：部分合成した語係数の辺成分は各合成項の辺成分の和（BF §1.2.4・§2.2.6）。
方針：合成の符号付き有限和へ線形写像を適用する。
規約：内側 arity 零も含み、各合成語は既存の正規化を使う。
使われ方：部分合成則の左辺を分割ごとに扱う入口。 -/
lemma edgeComponent_compositionOnWords {m n d e : ℕ} (u : BasisWord (m + 1) d)
    (v : BasisWord n e) (k : Fin (m + 1)) :
    edgeComponent A (m + n) (d + e) (compositionOnWords A u v k) =
      ∑ r : OverlapPartition (occurrenceCount u.val k) (n + e),
        compositionSign u v k r •
          edgeComponent A (m + n) (d + e) (compositeGenerator A u v k r) := by
  simp only [compositionOnWords, map_sum, map_zsmul]

/-- 概要：正の内側 arity の部分合成した辺成分は実際の合成語の成分和（BF §2.2.6）。
方針：正規化合成項と非退化基底語の一致を使う。
規約：内側語次数と外側語次数は任意。
使われ方：全合成項の切断を具体的な語の切断へ戻す。 -/
lemma edgeComponent_compositionOnWords_positive {m n d e : ℕ} (u : BasisWord (m + 1) d)
    (v : BasisWord n e) (k : Fin (m + 1)) (hn : 0 < n) :
    edgeComponent A (m + n) (d + e) (compositionOnWords A u v k) =
      ∑ r : OverlapPartition (occurrenceCount u.val k) (n + e),
        compositionSign u v k r • edgeComponentOnWord A (compositeBasisWord u v k r hn) := by
  simp only [edgeComponent_compositionOnWords, compositeGenerator_eq_basis A u v k _ hn,
    edgeComponent_basis]

/-- 概要：合成語の一つの切断の実際の符号付きテンソル値（BF §1.2.5・§2.2.6）。
方針：合成符号と切断符号を掛け、退化切断は零とする。
規約：出力全次数は d+e+1 の負。
使われ方：二段切断との項ごとの符号・出力比較。 -/
def compositionEdgeCutTerm {m n d e : ℕ} (u : BasisWord (m + 1) d) (v : BasisWord n e)
    (k : Fin (m + 1)) (r : OverlapPartition (occurrenceCount u.val k) (n + e)) (hn : 0 < n)
    (q : Fin (m + n + (d + e))) : (power (interval A) (m + n)).X (-((d + e + 1 : ℕ) : ℤ)) :=
  if h : EdgeNondegenerate (compositeBasisWord u v k r hn).val q then
    (compositionSign u v k r * edgeSign (compositeBasisWord u v k r hn).val q) •
      tensorVectorOfDegree A (m + n) (d + e + 1) (edgeOutput (compositeBasisWord u v k r hn) q)
        (edgeOutput_tupleDegree _ q h)
  else 0

/-- 概要：部分合成した実際の辺成分は分割と辺切断の全二重和（BF §2.2.6）。
方針：各実際の合成基底語の辺成分を展開して合成符号を各項へ配る。
規約：全ての退化項も同じ有限添字で零として保持する。
使われ方：部分合成則で二段切断の和へ移す正確な左辺。 -/
lemma edgeComponent_composition_cut_sum {m n d e : ℕ} (u : BasisWord (m + 1) d)
    (v : BasisWord n e) (k : Fin (m + 1)) (hn : 0 < n) :
    edgeComponent A (m + n) (d + e) (compositionOnWords A u v k) =
      ∑ r : OverlapPartition (occurrenceCount u.val k) (n + e),
        ∑ q : Fin (m + n + (d + e)), compositionEdgeCutTerm A u v k r hn q := by
  rw [edgeComponent_compositionOnWords_positive A u v k hn]
  apply Finset.sum_congr rfl
  intro r _
  rw [edgeComponentOnWord, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro q _
  unfold compositionEdgeCutTerm
  by_cases h : EdgeNondegenerate (compositeBasisWord u v k r hn).val q
  · rw [dite_eq_left h, dite_eq_left h]
    simp only [Int.cast_smul_eq_zsmul, smul_smul]
  · rw [dite_eq_right h, dite_eq_right h, smul_zero]

/-- 概要：部分合成後の複体余演算の辺入力は自然数次数の双線形成分（BF §2.2.6）。
方針：複体部分合成と余演算の負次数評価を使い、次数比較同型を打ち消す。
規約：全 arity と任意の二つの実際の χ の斉次元。
使われ方：複体射の部分合成則の左辺を有限切断和へ帰着する。 -/
lemma cochainAction_partialComposition_edge_tmul (m n d e : ℕ) (k : Fin (m + 1))
    (x : (complex A (m + 1)).X (-(d : ℤ))) (y : (complex A n).X (-(e : ℤ)))
    (z : (interval A).X (-1)) :
    (cochainAction A (m + n)).f (-((d + e + 1 : ℕ) : ℤ))
      (ιTensorObj (complex A (m + n)) (interval A) (-((d + e : ℕ) : ℤ)) (-1)
        (-((d + e + 1 : ℕ) : ℤ)) (by omega)
        ((complexPartialComposition A m n k).f (-((d + e : ℕ) : ℤ))
          (ιTensorObj (complex A (m + 1)) (complex A n) (-(d : ℤ)) (-(e : ℤ))
            (-((d + e : ℕ) : ℤ)) (by omega) (x ⊗ₜ[A] y)) ⊗ₜ[A] z)) =
      edgeInputBilinear A (m + n) (d + e)
        (partialComposition A m n d e k ((complexXIso A (m + 1) d).hom x)
          ((complexXIso A n e).hom y)) z := by
  rw [cochainAction_neg_edge A (m + n) (d + e), complexPartialComposition_neg_tmul,
    ModuleCat.hom_inv_apply]

end SerrePositivity.EInfinity.IntervalCuts
