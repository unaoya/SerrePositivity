module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.OutputLineRanks
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.RowOwners

/-!
模型。文献の定義との比較は後で
# 成功した Schedule の各行と lineRank の同定

概要：Berger–Fresse §1.5.7 の語の位置から元の table の行を一意に指定する。
方針：実際の抽出証跡の各行の長さと開始位置を Schedule の部分和へ移す。
規約：退化出力も含め、最終行の末尾まで扱う。
使われ方：k の出現位置と重なる分割の端点を元の抽出行へ割り当てる。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：元の抽出証跡の行内位置の lineRank は Schedule の行番号（BF §1.5.7）。
方針：選択行の長さと先行部分和を元の行長へ書き換える。
規約：行末自身は現在行の番号を持つ。
使われ方：内外成分の行数を元の Schedule の区間で数える。 -/
lemma _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionTrace.lineRank_schedule {n d : ℕ}
    {w : Fin (d + 1) → Equiv.Perm (Fin n)} {r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d}
    {picked : List (List (Fin n))} (ht : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionTrace (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r) [] picked)
    (v : Fin (n + d) → Fin n) (hout : picked.flatten = List.ofFn v)
    (i : Fin (d + 1)) (j : ℕ) (hj : j < (r.val i).val) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank v (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r i + j) = i.val := by
  have hl : picked.length = d + 1 := by
    simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows, List.length_ofFn] using ht.length
  have he : picked.map List.length = List.ofFn (fun k => (r.val k).val) := by
    simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows, List.map_ofFn, Function.comp_def] using ht.lengths
  have hi : i.val < picked.length := by rw [hl]; exact i.isLt
  have hrow : picked[i.val].length = (r.val i).val := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.picked_length_at r picked hl he i
  have hoff : ((picked.take i.val).map List.length).sum = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r i := by
    rw [List.map_take, he]
    rfl
  rw [← hoff]
  exact ht.lineRank_in_row v hout i.val hi j (by rw [hrow]; exact hj)

/-- 概要：成功した table の行内位置の lineRank はその行番号（BF §1.5.7）。
方針：元の成功から抽出証跡を取り出して同じ行番号の式を適用する。
規約：語の全射性や非退化性を仮定しない。
使われ方：TR の成功項だけを入力に元の行位置を評価する。 -/
lemma lineRank_schedule_of_reduction {n d : ℕ}
    (w : Fin (d + 1) → Equiv.Perm (Fin n)) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d)
    (v : Fin (n + d) → Fin n) (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r) [] = some (List.ofFn v))
    (i : Fin (d + 1)) (j : ℕ) (hj : j < (r.val i).val) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank v (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r i + j) = i.val := by
  obtain ⟨picked, ht, hout⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.extractionTrace_of_reduceRows _ _ _ h
  exact ht.lineRank_schedule v hout i j hj

/-- 概要：全ての出力位置の lineRank はその所属行の開始・終了区間を指定（BF §1.5.7）。
方針：元の出力位置の行内分解へ lineRank の評価を適用する。
規約：区間の右端は含めず、左端は含める。
使われ方：出現位置や分割端点を元の成功表の有限行添字へ移す。 -/
lemma lineRank_owner_of_reduction {n d : ℕ}
    (w : Fin (d + 1) → Equiv.Perm (Fin n)) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d)
    (v : Fin (n + d) → Fin n) (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r) [] = some (List.ofFn v))
    (p : Fin (n + d)) :
    ∃ i : Fin (d + 1), _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank v p.val = i.val ∧
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r i ≤ p.val ∧ p.val < _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r i + (r.val i).val := by
  let k : Fin (List.ofFn v).length := ⟨p.val, by simpa only [List.length_ofFn] using p.isLt⟩
  obtain ⟨i, pre, row, post, j, _, _, hoff, hlen, hpos⟩ :=
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.output_position_owner w r (List.ofFn v) h k
  have hj : j.val < (r.val i).val := by rw [← hlen]; exact j.isLt
  have hp : p.val = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r i + j.val := by
    change p.val = pre.length + j.val at hpos
    simpa only [hoff] using hpos
  refine ⟨i, ?_, ?_, ?_⟩
  · rw [hp]
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.lineRank_schedule_of_reduction w r v h i j.val hj
  · omega
  · omega

/-- 概要：成功した table の全出力位置の行番号は行数より小さい（BF §1.5.7）。
方針：所属行の有限添字の上界を使う。
規約：零 arity の空出力では位置が存在しない。
使われ方：lineRank そのものを元の行の有限添字として使う。 -/
lemma lineRank_lt_of_reduction {n d : ℕ}
    (w : Fin (d + 1) → Equiv.Perm (Fin n)) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d)
    (v : Fin (n + d) → Fin n) (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r) [] = some (List.ofFn v))
    (p : Fin (n + d)) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank v p.val < d + 1 := by
  obtain ⟨i, he, _, _⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.lineRank_owner_of_reduction w r v h p
  rw [he]
  exact i.isLt

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
