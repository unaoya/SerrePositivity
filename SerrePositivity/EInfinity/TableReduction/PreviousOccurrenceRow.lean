module

public import SerrePositivity.EInfinity.TableReduction.ScheduleRowEnds

/-!
# 直前の同値の出現が属する区切り行

概要：Berger–Fresse §1.4.4 の最終出現削除の受け取り行を成功 table から取り出す。
方針：直前の出現が区切りであることと、区切り列が行末列であることを使う。
規約：退化出力も含み、最終出現の係数を行番号で表示する。
使われ方：行長を増やす行と削除項の逆符号を特定する。
-/

@[expose] public section

namespace SerrePositivity.EInfinity.TableReduction

open Surjection

/-- 概要：直前の出現は成功 table の指定された非最終行末（BF §1.4.4）。
方針：前の出現の最大値を区切り列の所属から行末の添字へ戻す。
規約：削除位置に前の同値の出現があればよい。
使われ方：最終出現削除の受け取り行を指定する。 -/
lemma previousOccurrence_scheduleEnd {n d : ℕ}
    (w : Fin (d + 1) → Equiv.Perm (Fin n)) (r : Schedule n d)
    (out : List (Fin n)) (h : reduceRows (rows w r) [] = some out) (k : Fin out.length)
    (hp : (previousOccurrences (fun j : Fin out.length => out[j.val]) k).Nonempty) :
    ∃ i : Fin d, scheduleEnd r i =
      ((previousOccurrences (fun j : Fin out.length => out[j.val]) k).max' hp).val := by
  let p := (previousOccurrences (fun j : Fin out.length => out[j.val]) k).max' hp
  obtain ⟨picked, he, hn, hl, hlengths, hrep⟩ := rowEnds_of_reduction w r out h
  have hc : Caesura (fun j : Fin out.length => out[j.val]) p :=
    caesura_previousOccurrence _ k hp
  have hm := (rowEnds_caesura_iff picked out hrep p).mp hc
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp hm
  have hjb : j.val < d := by
    have hb := j.isLt
    have hlen : (rowEndPositions picked).length = d := by
      rw [rowEndPositions_length, hl, Nat.add_sub_cancel]
    omega
  let i : Fin d := ⟨j.val, hjb⟩
  have hlookup : (rowEndPositions picked)[i.val]? = some p.val := by
    rw [List.getElem?_eq_getElem j.isLt]
    exact congrArg some hj
  have hpos := rowEnds_eq_scheduleEnds r picked hn hl hlengths i
  exact ⟨i, Option.some.inj (hpos.symm.trans hlookup)⟩

/-- 概要：最終出現削除の係数は直前の出現が属する行番号の逆符号（BF §1.4.4）。
方針：直前の出現の行末係数と最終出現の符号反転を組み合わせる。
規約：非全射・退化出力も含む。
使われ方：相殺相手の行末削除の符号と比較する。 -/
lemma final_deletion_coefficient_receiver {n d : ℕ}
    (w : Fin (d + 1) → Equiv.Perm (Fin n)) (r : Schedule n d)
    (out : List (Fin n)) (h : reduceRows (rows w r) [] = some out) (k : Fin out.length)
    (hf : ¬ Caesura (fun j : Fin out.length => out[j.val]) k)
    (hp : (previousOccurrences (fun j : Fin out.length => out[j.val]) k).Nonempty) :
    ∃ i : Fin d,
      scheduleEnd r i =
        ((previousOccurrences (fun j : Fin out.length => out[j.val]) k).max' hp).val ∧
      deletionCoefficient (fun j : Fin out.length => out[j.val]) k = -((-1 : ℤ) ^ i.val) := by
  obtain ⟨i, hi⟩ := previousOccurrence_scheduleEnd w r out h k hp
  refine ⟨i, hi, ?_⟩
  have he := deletionCoefficient_schedule_rowEnd w r out h i
    ((previousOccurrences (fun j : Fin out.length => out[j.val]) k).max' hp) hi
  rw [deletionCoefficient_final _ k hf hp, he]

end SerrePositivity.EInfinity.TableReduction
