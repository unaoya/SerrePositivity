module

public import SerrePositivity.EInfinity.TableReduction.ScheduleLineRanks
public import SerrePositivity.EInfinity.TableReduction.RowInterior

/-!
# 語の位置から決まる成功表の有限行添字

概要：Berger–Fresse §1.5.7 の出現位置や成分端点の所属行を lineRank 自身で指定する。
方針：成功抽出の行番号の上界を使い、行内区間の一意性と単調性を公開する。
規約：値は任意に選ぶのではなく語の lineRank に等しい。
使われ方：元の二表の成分区間を実際の shuffle の格子頂点へ移す。
-/

@[expose] public section

namespace SerrePositivity.EInfinity.TableReduction

open Surjection

/-- 概要：成功表の指定出力位置を含む有限行添字（BF §1.5.7）。
方針：lineRank を行数の上界の証明で包む。
規約：計算する自然数値は語だけに依存する。
使われ方：合成の各端点に対応する元の二つの行を指定する。 -/
def reductionRow {n d : ℕ} (w : Fin (d + 1) → Equiv.Perm (Fin n)) (r : Schedule n d)
    (v : Fin (n + d) → Fin n) (h : reduceRows (rows w r) [] = some (List.ofFn v))
    (p : Fin (n + d)) : Fin (d + 1) :=
  ⟨lineRank v p.val, lineRank_lt_of_reduction w r v h p⟩

/-- 概要：有限行添字の位置は元の Schedule のその行内にある（BF §1.5.7）。
方針：成功表の所属行の存在を lineRank の値で一意に照合する。
規約：右端を含まない行内区間。
使われ方：成分端点で元の抽出を前後に分ける。 -/
lemma reductionRow_bounds {n d : ℕ}
    (w : Fin (d + 1) → Equiv.Perm (Fin n)) (r : Schedule n d)
    (v : Fin (n + d) → Fin n) (h : reduceRows (rows w r) [] = some (List.ofFn v))
    (p : Fin (n + d)) :
    scheduleOffset r (reductionRow w r v h p) ≤ p.val ∧
      p.val < scheduleOffset r (reductionRow w r v h p) +
        (r.val (reductionRow w r v h p)).val := by
  obtain ⟨i, he, hlo, hhi⟩ := lineRank_owner_of_reduction w r v h p
  have hi : reductionRow w r v h p = i := Fin.ext he
  rw [hi]
  exact ⟨hlo, hhi⟩

/-- 概要：語から決まる所属行は元の行内区間で特徴付けられる（BF §1.5.7）。
方針：同じ位置を含む行の一意性を使う。
規約：最終行も含む。
使われ方：行内の分割位置から元の有限行添字を回収する。 -/
lemma reductionRow_eq_iff {n d : ℕ}
    (w : Fin (d + 1) → Equiv.Perm (Fin n)) (r : Schedule n d)
    (v : Fin (n + d) → Fin n) (h : reduceRows (rows w r) [] = some (List.ofFn v))
    (p : Fin (n + d)) (i : Fin (d + 1)) :
    reductionRow w r v h p = i ↔
      scheduleOffset r i ≤ p.val ∧ p.val < scheduleOffset r i + (r.val i).val := by
  have hb := reductionRow_bounds w r v h p
  constructor
  · intro he
    simpa only [he] using hb
  · intro hi
    exact row_unique_of_bounds r _ i p.val hb.1 hb.2 hi.1 hi.2

/-- 概要：出力位置が進むとその所属行は戻らない（BF §1.5.7）。
方針：lineRank の単調性を有限行添字へ移す。
規約：同じ行内の位置では等しくてよい。
使われ方：成分区間の始行と終行を順序付きにする。 -/
lemma reductionRow_mono {n d : ℕ}
    (w : Fin (d + 1) → Equiv.Perm (Fin n)) (r : Schedule n d)
    (v : Fin (n + d) → Fin n) (h : reduceRows (rows w r) [] = some (List.ofFn v)) :
    Monotone (reductionRow w r v h) := by
  intro p q hpq
  exact lineRank_mono v hpq

end SerrePositivity.EInfinity.TableReduction
