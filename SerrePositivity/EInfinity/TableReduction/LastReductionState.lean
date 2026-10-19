module

public import SerrePositivity.EInfinity.TableReduction.LastCursor
public import SerrePositivity.EInfinity.TableReduction.ReductionInterval
public import SerrePositivity.EInfinity.Surjection.LineRanks

/-!
# 語の最終位置における元の進行状態の一文字行

概要：Berger–Fresse §1.5.7 の元の内側最終位置の利用可能行を仮定なしに一文字へ同定する。
方針：語の最後の lineRank が次数であることと元の最終行の飽和性を合わせる。
規約：指定した有限位置は元の語の最後の位置。
使われ方：最後の指定値より後の水平成分を固定内側で抽出する。
-/

@[expose] public section

namespace SerrePositivity.EInfinity.TableReduction

open Surjection

/-- 概要：元の語の最後の位置の進行状態の利用可能行は末尾一文字（BF §1.5.7）。
方針：語から決まる所属行を最終行へ同定し、その位置の元の cursor に適用する。
規約：元の成功だけを使い、一文字行を別途仮定しない。
使われ方：最終水平成分の内側の singleton 条件を供給する。 -/
lemma reductionRemoved_last_singleton {n d : ℕ}
    (w : Fin (d + 1) → Equiv.Perm (Fin n)) (r : Schedule n d) (v : BasisWord n d)
    (h : reduceRows (rows w r) [] = some (List.ofFn v.val))
    (q : Fin (n + d)) (hq : q.val + 1 = n + d) :
    available (reductionRemoved w r v.val h q)
      (List.ofFn (w (reductionRow w r v.val h q)).symm) = [v.val q] := by
  have hi : reductionRow w r v.val h q = Fin.last d := by
    apply Fin.ext
    change lineRank v.val q.val = d
    have hq' : q.val = n + d - 1 := by omega
    rw [hq', lineRank_last]
  change available ((reductionCursor w r v.val h q).removed ++
    (available (reductionCursor w r v.val h q).removed
      (vertexRow w (reductionRow w r v.val h q))).take (reductionColumn w r v.val h q).val)
    (vertexRow w (reductionRow w r v.val h q)) = _
  exact (reductionCursor w r v.val h q).final_available_singleton hi q hq
    (reductionColumn w r v.val h q) (reductionColumn_position w r v.val h q)

end SerrePositivity.EInfinity.TableReduction
