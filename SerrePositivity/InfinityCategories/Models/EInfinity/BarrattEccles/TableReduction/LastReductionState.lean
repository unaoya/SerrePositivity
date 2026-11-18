module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.LastCursor
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReductionInterval
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.LineRanks

/-!
模型。文献の定義との比較は後で
# 語の最終位置における元の進行状態の一文字行

概要：Berger–Fresse §1.5.7 の元の内側最終位置の利用可能行を仮定なしに一文字へ同定する。
方針：語の最後の lineRank が次数であることと元の最終行の飽和性を合わせる。
規約：指定した有限位置は元の語の最後の位置。
使われ方：最後の指定値より後の水平成分を固定内側で抽出する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：元の語の最後の位置の進行状態の利用可能行は末尾一文字（BF §1.5.7）。
方針：語から決まる所属行を最終行へ同定し、その位置の元の cursor に適用する。
規約：元の成功だけを使い、一文字行を別途仮定しない。
使われ方：最終水平成分の内側の singleton 条件を供給する。 -/
lemma reductionRemoved_last_singleton {n d : ℕ}
    (w : Fin (d + 1) → Equiv.Perm (Fin n)) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d)
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r) [] = some (List.ofFn v.val))
    (q : Fin (n + d)) (hq : q.val + 1 = n + d) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionRemoved w r v.val h q)
      (List.ofFn (w (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionRow w r v.val h q)).symm) = [v.val q] := by
  have hi : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionRow w r v.val h q = Fin.last d := by
    apply Fin.ext
    change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank v.val q.val = d
    have hq' : q.val = n + d - 1 := by omega
    rw [hq', _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank_last]
  change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionCursor w r v.val h q).removed ++
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionCursor w r v.val h q).removed
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionRow w r v.val h q))).take (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionColumn w r v.val h q).val)
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionRow w r v.val h q)) = _
  exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionCursor w r v.val h q).final_available_singleton hi q hq
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionColumn w r v.val h q) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionColumn_position w r v.val h q)

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
