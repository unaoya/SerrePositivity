module

public import SerrePositivity.EInfinity.TableReduction.ReductionInterval
public import SerrePositivity.EInfinity.TableReduction.PrefixUniqueness
public import SerrePositivity.EInfinity.Surjection.LineRanks

/-!
# 元の語の最初の位置の空の進行状態

概要：Berger–Fresse §1.5.7 の成分列を空の除外状態から開始できることを示す。
方針：最初の行番号と行内列は零であり、空の先行証跡の状態は空と一意に決まる。
規約：元の成功抽出の選択証明書に依存しない。
使われ方：全成分を連結した実際の合成表の初期状態を閉じる。
-/

@[expose] public section

namespace SerrePositivity.EInfinity.TableReduction

open Surjection

/-- 概要：元の語の最初の位置までの進行状態は空（BF §1.5.7）。
方針：空の先行行列の証跡の一意性と行内前半の長さ零を使う。
規約：最初の位置の値は任意。
使われ方：合成表の全成分列の抽出を空の除外状態から開始する。 -/
lemma reductionRemoved_first_eq_nil {n d : ℕ}
    (w : Fin (d + 1) → Equiv.Perm (Fin n)) (r : Schedule n d)
    (v : Fin (n + d) → Fin n) (h : reduceRows (rows w r) [] = some (List.ofFn v))
    (p : Fin (n + d)) (hp : p.val = 0) : reductionRemoved w r v h p = [] := by
  let c := reductionCursor w r v h p
  have hb : c.before = [] := by
    apply List.length_eq_zero_iff.mp
    rw [c.before_length]
    change lineRank v p.val = 0
    rw [hp, lineRank_zero]
  have ht := c.before_trace
  rw [hb] at ht
  have hm : c.removed = [] := (ht.unique (ExtractionPrefix.nil ([] : List (Fin n)))).2
  have hj : (reductionColumn w r v h p).val = 0 := by
    change p.val - scheduleOffset r (reductionRow w r v h p) = 0
    rw [hp, Nat.zero_sub]
  change c.removed ++ (available c.removed (vertexRow w (reductionRow w r v h p))).take
    (reductionColumn w r v h p).val = []
  rw [hj, List.take_zero, List.append_nil, hm]

end SerrePositivity.EInfinity.TableReduction
