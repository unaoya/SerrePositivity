module

public import SerrePositivity.EInfinity.TableReduction.ScheduleBlock

/-!
# 指定された一行の元の抽出状態

概要：Berger–Fresse §1.5.7 の成分端点で元の成功抽出を一行の前後に分ける。
方針：行リストを指定添字で分け、先行抽出・現在行・後続抽出を同じ成功から取り出す。
規約：現在行は既存の逆置換行 vertexRow そのもの。
使われ方：内外の除外状態と利用可能行から合成抽出の一段を構成する。
-/

@[expose] public section

namespace SerrePositivity.EInfinity.TableReduction

/-- 概要：元の成功表の指定行における抽出状態の証明書（BF §1.5.7）。
方針：先行証跡・現在行の長さ条件・後続抽出を保持する。
規約：出力が退化していても構成する。
使われ方：語の位置から決まった行へ合成の一段の成功規則を適用する。 -/
structure ScheduleRowCursor {n d : ℕ} (w : Fin (d + 1) → Equiv.Perm (Fin n))
    (r : Schedule n d) (i : Fin (d + 1)) (out : List (Fin n)) where
  before : List (List (Fin n) × ℕ)
  after : List (List (Fin n) × ℕ)
  selectedBefore : List (List (Fin n))
  removed : List (Fin n)
  tail : List (Fin n)
  split : rows w r = before ++ (vertexRow w i, (r.val i).val) :: after
  before_length : before.length = i.val
  before_trace : ExtractionPrefix before [] selectedBefore removed
  bound : (r.val i).val ≤ (available removed (vertexRow w i)).length
  tail_success : reduceRows after
    (removed ++ (available removed (vertexRow w i)).take ((r.val i).val - 1)) = some tail
  output_eq : out = selectedBefore.flatten ++
    ((available removed (vertexRow w i)).take (r.val i).val ++ tail)
  prefix_length : selectedBefore.flatten.length = scheduleOffset r i

/-- 概要：成功した table の任意の指定行の元の抽出状態を取り出す（BF §1.5.7）。
方針：take/drop による行分割と元の抽出の先行部分を照合する。
規約：現在行の選択語や状態を別途仮定しない。
使われ方：元の二つの成功表から合成行の除外状態を得る。 -/
lemma scheduleRowCursor_nonempty {n d : ℕ} (w : Fin (d + 1) → Equiv.Perm (Fin n))
    (r : Schedule n d) (i : Fin (d + 1)) (out : List (Fin n))
    (h : reduceRows (rows w r) [] = some out) : Nonempty (ScheduleRowCursor w r i out) := by
  let before := (rows w r).take i.val
  let after := (rows w r).drop (i.val + 1)
  have hi : i.val < (rows w r).length := by
    simpa only [rows, List.length_ofFn] using i.isLt
  have hsplit : rows w r = before ++ (vertexRow w i, (r.val i).val) :: after := by
    calc
      _ = (rows w r).take i.val ++ (rows w r).drop i.val :=
        (List.take_append_drop i.val (rows w r)).symm
      _ = _ := by
        rw [List.drop_eq_getElem_cons hi]
        simp only [rows, List.getElem_ofFn]
        rfl
  have hbefore : before.length = i.val := by
    exact List.length_take_of_le (by omega)
  have hsuccess : reduceRows (before ++ (vertexRow w i, (r.val i).val) :: after) [] =
      some out := by rw [← hsplit]; exact h
  obtain ⟨picked, removed, restOut, hp, ht, hout⟩ :=
    extractionPrefix_of_reduceRows before _ [] out hsuccess
  obtain ⟨_, hb, tail, htail, hrest⟩ := reduceRows_cons_success _ _ _ _ _ ht
  refine ⟨⟨before, after, picked, removed, tail, hsplit, hbefore, hp, hb, htail, ?_, ?_⟩⟩
  · rw [hout, hrest]
  · exact hp.output_length.trans (rows_prefix_sum w r before _ hsplit i hbefore)

end SerrePositivity.EInfinity.TableReduction
