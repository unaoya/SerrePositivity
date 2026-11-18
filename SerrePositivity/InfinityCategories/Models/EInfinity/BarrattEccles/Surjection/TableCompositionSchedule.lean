module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionRowCount
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.SuccessfulRowBounds

/-!
模型。文献の定義との比較は後で
# 実際の全融合表の行長から合成 Schedule を構成する

概要：Berger–Fresse §1.5.7 の融合行列の選択長さを実際の有限 Schedule にまとめる。
方針：全行の長さ・抽出成功・合成語の総長から有限上界、正性、総和を得る。
規約：元の二つの成功と分割だけを使う。
使われ方：経路行列の照合後、元の table reduction の正方向の項を供給する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData

open _root_.SerrePositivity.EInfinity.BarrattEccles _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：融合後の全ての実際の行は合成 arity と同じ長さ（BF §1.5.7）。
方針：各行が元の合成置換の逆像列であることを境界融合で保存する。
規約：選択長さではなく元の行全体の長さ。
使われ方：成功した各選択長さを有限な Schedule の添字へ包む。 -/
lemma fusedRows_row_length {m n d e : ℕ} (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData m n d e)
    (i : ℕ) (hi : i ≤ c.count) :
    ∀ row ∈ (c.fusedRows i).map Prod.fst, row.length = m + n := by
  have hh : ∀ row ∈ (c.horizontalRows i).map Prod.fst, row.length = m + n := by
    intro row hr
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData.horizontalRows, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.fixedInnerRows, List.map_map, List.mem_map] at hr
    obtain ⟨p, _, hp⟩ := hr
    subst row
    exact List.length_ofFn
  by_cases hlt : i < c.count
  · have hv : ∀ row ∈ (c.verticalRows ⟨i, hlt⟩).map Prod.fst, row.length = m + n := by
      intro row hr
      simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData.verticalRows, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.fixedOuterRows, List.map_map, List.mem_map] at hr
      obtain ⟨p, _, hp⟩ := hr
      subst row
      exact List.length_ofFn
    have hhn : c.horizontalRows i ≠ [] := by
      have := c.horizontalRows_length i
      intro he; rw [he] at this; simp only [List.length_nil] at this; omega
    have hvn : c.verticalRows ⟨i, hlt⟩ ≠ [] := by
      have := c.verticalRows_length ⟨i, hlt⟩
      intro he; rw [he] at this; simp only [List.length_nil] at this; omega
    have hn := (c.fusedRows_nonempty_head (i + 1) (by omega)).1
    have hm := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.fuseBoundary_ne_nil _ _ hvn hn
    have hnext := c.fusedRows_row_length (i + 1) (by omega)
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData.fusedRows, dite_eq_left hlt]
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.fuseBoundary_all_rows _ _ _ hhn hm hh
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.fuseBoundary_all_rows _ _ _ hvn hn hv hnext)
  · have he : i = c.count := by omega
    subst i
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData.fusedRows, dite_eq_right (Nat.lt_irrefl _)]
    exact hh
termination_by c.count - i
decreasing_by omega

/-- 概要：融合表の有限頂点添字で指定した実際の選択長さ（BF §1.5.7）。
方針：証明済みの d+e+1行という長さで元の行を評価する。
規約：元の行長自体を保持する。
使われ方：合成 Schedule の値。 -/
noncomputable def fusedLength {m n d e : ℕ} (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData m n d e)
    (i : Fin (d + e + 1)) : ℕ :=
  ((c.fusedRows 0)[i.val]'(by rw [c.fusedRows_length]; exact i.isLt)).2

/-- 概要：融合表の各実際の選択長さは正で合成 arity 以下（BF §1.5.7）。
方針：実際の合成語抽出成功から全行長の条件を取り出す。
規約：Schedule の条件を新たに仮定しない。
使われ方：各行長を Fin(m+n+1)へ包む。 -/
lemma fusedLength_bounds {m n d e : ℕ} (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData m n d e)
    (i : Fin (d + e + 1)) : 0 < c.fusedLength i ∧ c.fusedLength i ≤ m + n := by
  have hm : (c.fusedRows 0)[i.val]'(by rw [c.fusedRows_length]; exact i.isLt) ∈
      c.fusedRows 0 := List.getElem_mem _
  have hb := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_row_bounds _ _ _ c.fused_success_compositeWord _ hm
  have hl := c.fusedRows_row_length 0 (Nat.zero_le _) _ (List.mem_map.mpr ⟨_, hm, rfl⟩)
  change 0 < c.fusedLength i ∧ c.fusedLength i ≤ _ at hb
  exact ⟨hb.1, by simpa only [hl] using hb.2⟩

/-- 概要：有限添字の融合行長列は元の実際の行長列に一致（BF §1.5.7）。
方針：同じ長さのリストの各有限位置を比較する。
規約：融合後の行順を保つ。
使われ方：実際の抽出出力長から行長の有限和を求める。 -/
lemma fusedLength_list {m n d e : ℕ} (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData m n d e) :
    List.ofFn c.fusedLength = (c.fusedRows 0).map Prod.snd := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_map, c.fusedRows_length]
  · intro i hi hj
    simp only [List.getElem_ofFn, List.getElem_map, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData.fusedLength]

/-- 概要：融合行長の総和は合成 arity＋合成次数（BF §1.5.7）。
方針：実際の合成語の長さを抽出成功の総行長に移す。
規約：部分語の総長を再び仮定しない。
使われ方：合成 Schedule の総和条件。 -/
lemma fusedLength_sum {m n d e : ℕ} (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData m n d e) :
    (∑ i, c.fusedLength i) = m + n + (d + e) := by
  rw [← List.sum_ofFn, c.fusedLength_list, ← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_length _ _ _ c.fused_success_compositeWord]
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeWord_length c.outerWord c.innerWord c.slot c.cuts

/-- 概要：元の二表から構成した全融合表の実際の Schedule（BF §1.5.7）。
方針：実際の行長の上界・正性・総和を既存の有限型へまとめる。
規約：経路上の置換列との照合は別途行う。
使われ方：一般の TR 合成保存の正方向の行長添字。 -/
noncomputable def fusedSchedule {m n d e : ℕ} (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData m n d e) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule (m + n) (d + e) :=
  ⟨(fun i => ⟨c.fusedLength i, by have := (c.fusedLength_bounds i).2; omega⟩),
    (fun i => (c.fusedLength_bounds i).1), c.fusedLength_sum⟩

/-- 概要：融合 Schedule で元の行の列を使えば実際の全融合行列を復元できる（BF §1.5.7）。
方針：元の行の列と選択長さの列の両射影を zip で復元する。
規約：置換列の行一致は明示した入力。経路上の列との一致は後続で証明する。
使われ方：経路行列の照合を実際の抽出成功へ移す。 -/
lemma rows_fusedSchedule_of_fst {m n d e : ℕ} (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData m n d e)
    (w : Fin (d + e + 1) → Equiv.Perm (Fin (m + n)))
    (hw : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w c.fusedSchedule).map Prod.fst = (c.fusedRows 0).map Prod.fst) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w c.fusedSchedule = c.fusedRows 0 := by
  have hl : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w c.fusedSchedule).map Prod.snd = (c.fusedRows 0).map Prod.snd := by
    simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows, List.map_ofFn, Function.comp_def, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData.fusedSchedule] using c.fusedLength_list
  calc
    _ = ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w c.fusedSchedule).map Prod.fst).zip
        ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w c.fusedSchedule).map Prod.snd) := by
      simp only [List.zip_map', Prod.eta]
      exact (List.map_id' _).symm
    _ = ((c.fusedRows 0).map Prod.fst).zip ((c.fusedRows 0).map Prod.snd) := by rw [hw, hl]
    _ = c.fusedRows 0 := by
      simp only [List.zip_map', Prod.eta]
      exact List.map_id' _

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData
