module

public import SerrePositivity.EInfinity.IntervalCuts.FamilyBlocks
public import SerrePositivity.EInfinity.IntervalCuts.NestedOutputValues

/-!
# 二段切断の出力族を前後ブロックへ分ける

概要：Berger–Fresse §2.2.6 の全二段出力族を実際の余代入のブロックの順序で表す。
方針：内側の辺出力族または一定頂点族を取り、一般の族の置換表示を使う。
規約：内側 arity 零の族も定義し、全次数の式は全分岐で成立する。
使われ方：二段作用の実際の面テンソル値と共通出力族の同定。
-/

@[expose] public section

namespace SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut

open Surjection

/-- 概要：二段切断の内側作用だけの出力族（BF §2.2.6）。
方針：辺入力は内側切断の出力、頂点入力は外側指定出力の一定族とする。
規約：実際の全出力族の挿入区間と同じ順序。
使われ方：前方・内側・後方の面テンソルの連結表示。 -/
def innerOutputFamily {m n d e : ℕ} {u : BasisWord (m + 1) d} {v : BasisWord n e}
    {k : Fin (m + 1)} (a : NestedEdgeCut u v k) (j : Fin n) : Simplex :=
  match a.val.2 with
  | none => edgeOutput u a.val.1 k
  | some q => edgeOutput v q j

/-- 概要：二段切断の全出力族は外側指定出力の内側族による置換（BF §2.2.6）。
方針：残り・挿入ラベルによる両定義を照合する。
規約：内側の辺・頂点入力を同時に扱う。
使われ方：一般の族のブロック表示へ接続する。 -/
lemma outputFamily_eq_insertion {m n d e : ℕ} {u : BasisWord (m + 1) d}
    {v : BasisWord n e} {k : Fin (m + 1)} (a : NestedEdgeCut u v k) :
    a.outputFamily = insertionFamily (edgeOutput u a.val.1) a.innerOutputFamily k := by
  funext j
  unfold outputFamily insertionFamily innerOutputFamily
  cases operadInsertionEquiv m n k j <;> rfl

/-- 概要：二段切断の全出力族は前方・内側・後方のブロック連結（BF §2.2.6）。
方針：外側指定出力の置換へ一般の三ブロック表示を適用する。
規約：合成出力 arity への移送を最後に明示する。
使われ方：実際の余代入の面テンソル評価と出力族を一致させる。 -/
lemma outputFamily_eq_blocks {m n d e : ℕ} {u : BasisWord (m + 1) d}
    {v : BasisWord n e} {k : Fin (m + 1)} (a : NestedEdgeCut u v k) :
    a.outputFamily =
      Fin.append (prefixFamily (edgeOutput u a.val.1) k)
        (Fin.append a.innerOutputFamily (suffixFamily (edgeOutput u a.val.1) k)) ∘
        Fin.cast (by omega : m + n = k.val + (n + (m - k.val))) := by
  rw [outputFamily_eq_insertion]
  exact insertionFamily_eq_blocks _ _ _

/-- 概要：内側出力族の次数は内側語次数と指定入力の次数の和（BF §2.2.3）。
方針：辺入力では内側切断の次数公式、頂点入力では内側次数零と一定頂点族を使う。
規約：内側 arity の正性を追加しない。
使われ方：実際の内側余演算の整数次数をブロック評価と一致させる。 -/
lemma innerOutputFamily_tupleDegree {m n d e : ℕ} {u : BasisWord (m + 1) d}
    {v : BasisWord n e} {k : Fin (m + 1)} (a : NestedEdgeCut u v k) :
    tupleDegree n a.innerOutputFamily = e + simplexDegree (edgeOutput u a.val.1 k) := by
  have H := a.property.2
  cases ha : a.val.2 with
  | none =>
    rw [ha] at H
    have hd : simplexDegree (edgeOutput u a.val.1 k) = 0 := by
      rw [simplexDegree_eq_edge_indicator, ite_eq_right H.1]
    simp only [innerOutputFamily, ha, tupleDegree_eq_sum, hd,
      Finset.sum_const_zero, H.2, Nat.add_zero]
  | some q =>
    rw [ha] at H
    have hf : a.innerOutputFamily = edgeOutput v q := by
      funext j
      simp only [innerOutputFamily, ha]
    rw [hf, edgeOutput_tupleDegree v q H.2, H.1, simplexDegree_edge]

end SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut
