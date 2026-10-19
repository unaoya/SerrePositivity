module

public import SerrePositivity.EInfinity.TableReduction.ReductionRows
public import SerrePositivity.EInfinity.Surjection.OccurrenceOrder

/-!
# 同じ文字の順次出現が属する抽出行の順序

概要：Berger–Fresse §1.5.7 の外側指定値の各出現を異なる元の抽出行へ対応させる。
方針：同じ行は重複しないため、同じ値の前の出現はその行の開始位置より前にある。
規約：出力の隣接非退化性は要求しない。
使われ方：出現で切った外側成分に元の行の重ならない進行順を与える。
-/

@[expose] public section

namespace SerrePositivity.EInfinity.TableReduction

open Surjection

/-- 概要：同じ文字の前の出現は元の成功表で狭義に前の行に属する（BF §1.5.7）。
方針：後の位置の所属行の重複のなさから前の位置を行開始位置より前へ移す。
規約：成功表自体が退化出力を持つ場合も扱う。
使われ方：外側指定値の各出現の有限行添字を区別する。 -/
lemma reductionRow_lt_of_repeat {n d : ℕ}
    (w : Fin (d + 1) → Equiv.Perm (Fin n)) (r : Schedule n d)
    (v : Fin (n + d) → Fin n) (h : reduceRows (rows w r) [] = some (List.ofFn v))
    (p q : Fin (n + d)) (hpq : p < q) (hv : v p = v q) :
    reductionRow w r v h p < reductionRow w r v h q := by
  let kp : Fin (List.ofFn v).length := ⟨p.val, by simpa only [List.length_ofFn] using p.isLt⟩
  let kq : Fin (List.ofFn v).length := ⟨q.val, by simpa only [List.length_ofFn] using q.isLt⟩
  obtain ⟨i, pre, row, post, j, hout, hn, hoff, hlen, hpos⟩ :=
    output_position_owner w r (List.ofFn v) h kq
  have hp : p.val < pre.length := by
    exact previous_position_before_owner (List.ofFn v) pre row post hout hn kq kp j hpos
      hpq (by simpa only [List.getElem_ofFn] using hv)
  have hq : reductionRow w r v h q = i := by
    apply (reductionRow_eq_iff w r v h q i).mpr
    change q.val = pre.length + j.val at hpos
    have hj := j.isLt
    constructor <;> omega
  rw [hq]
  by_contra hnot
  have hle : i ≤ reductionRow w r v h p := le_of_not_gt hnot
  have hm := (scheduleOffset_strictMono r).monotone hle
  have hb := (reductionRow_bounds w r v h p).1
  omega

/-- 概要：指定値の出現順の所属行列は狭義単調（BF §1.5.7）。
方針：出現位置の狭義単調性と同じ値の行の順序を合成する。
規約：出現回数零の場合も空の列として成立する。
使われ方：各内側成分を異なる外側の指定出現の行へ挿入する。 -/
lemma occurrence_reductionRow_strictMono {n d : ℕ}
    (w : Fin (d + 1) → Equiv.Perm (Fin n)) (r : Schedule n d)
    (v : Fin (n + d) → Fin n) (h : reduceRows (rows w r) [] = some (List.ofFn v))
    (k : Fin n) :
    StrictMono (fun j : Fin (occurrenceCount v k) =>
      reductionRow w r v h (occurrenceAt v k j)) := by
  intro i j hij
  exact reductionRow_lt_of_repeat w r v h (occurrenceAt v k i) (occurrenceAt v k j)
    (occurrenceAt_strictMono v k hij)
    ((occurrenceAt_value v k i).trans (occurrenceAt_value v k j).symm)

end SerrePositivity.EInfinity.TableReduction
