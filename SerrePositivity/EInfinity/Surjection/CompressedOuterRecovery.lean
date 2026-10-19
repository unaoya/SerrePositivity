module

public import SerrePositivity.EInfinity.Surjection.OuterTableRecovery
public import SerrePositivity.EInfinity.Surjection.AdjacentCollapseConcatenation
public import SerrePositivity.EInfinity.TableReduction.RepeatedRowCompression

/-!
# 重複行を融合した外側表の成功と元の外側語

概要：Berger–Fresse §1.5.8 の合成表から外側の重複行を融合した成功表を得る。
方針：全外側抽出を復元し、行融合の成功と各行縮約の全語縮約への一致を使う。
規約：外側表の行数と元の shuffle の外側次数の一致は別途照合する。
使われ方：一般の TR 部分合成保存の逆構成で外側の候補表を供給する。
-/

@[expose] public section

namespace SerrePositivity.EInfinity.Surjection.CompositeRecovery

open BarrattEccles TableReduction

/-- 概要：各選択行を外側へ縮約してから全体を縮約しても元の外側語（BF §1.5.8）。
方針：外側写像を平坦化と交換し、各行の縮約を全語の縮約へ戻す。
規約：行境界にも連続する同じ外側値を許す。
使われ方：圧縮外側表の出力を元の合成出力から復元した語へ同定する。 -/
lemma collapse_outer_picked {m n : ℕ} (k : Fin (m + 1))
    (picked : List (List (Fin (m + n)))) :
    AdjacentCollapse.collapse (picked.map (outerWord k)).flatten = outerWord k picked.flatten := by
  have he : picked.map (outerWord k) =
      (picked.map (List.map (outerLabel k))).map AdjacentCollapse.collapse := by
    rw [List.map_map]
    rfl
  change AdjacentCollapse.collapse (picked.map (outerWord k)).flatten =
    AdjacentCollapse.collapse (picked.flatten.map (outerLabel k))
  rw [he, AdjacentCollapse.collapse_flatten, List.map_flatten]

/-- 概要：復元外側表の各行は非重複（BF §1.5.8）。
方針：各行が元の外側逆置換の全値の列であることを zipWith で追跡する。
規約：選択語の行数に関する仮定は不要。
使われ方：復元表全体に隣接重複行の圧縮成功を適用する。 -/
lemma recoveredOuterTable_rows_nodup {m n : ℕ} (k : Fin (m + 1))
    (entries : List (Equiv.Perm (Fin (m + 1)) × Equiv.Perm (Fin n) × ℕ))
    (picked : List (List (Fin (m + n)))) :
    ∀ p ∈ recoveredOuterTable k entries picked, p.1.Nodup := by
  induction entries generalizing picked with
  | nil => simp [recoveredOuterTable]
  | cons entry entries ih =>
    cases picked with
    | nil => simp [recoveredOuterTable]
    | cons word picked =>
      intro p hp
      simp only [recoveredOuterTable, List.zipWith_cons_cons, List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact List.nodup_ofFn_ofInjective entry.1.symm.injective
      · exact ih picked p hp

/-- 概要：任意の成功合成表から重複外側行を融合した成功表を得る（BF §1.5.8）。
方針：全外側抽出成功に全行融合を適用し、縮約出力を元の合成語の外側復元へ戻す。
規約：圧縮出力の縮約が元の外側語に等しい。非退化性と元の行数の照合は別途行う。
使われ方：元の外側成功表と行長 Schedule を逆構成する。 -/
lemma compressed_outer_table_success {m n : ℕ} (k : Fin (m + 1))
    (entries : List (Equiv.Perm (Fin (m + 1)) × Equiv.Perm (Fin n) × ℕ))
    (removed out : List (Fin (m + n)))
    (h : reduceRows (mixedTable k entries) removed = some out) :
    ∃ picked finish out', ExtractionPrefix (mixedTable k entries) removed picked finish ∧
      out = picked.flatten ∧
      reduceRows (compressRows (recoveredOuterTable k entries picked)) (outerRemoved k removed) =
        some out' ∧ AdjacentCollapse.collapse out' = outerWord k out := by
  obtain ⟨picked, finish, hp, ho, hs⟩ := outer_table_success k entries removed out h
  obtain ⟨out', ht, hc⟩ := compressRows_success _ _ _
    (recoveredOuterTable_rows_nodup k entries picked) hs
  refine ⟨picked, finish, out', hp, ho, ht, ?_⟩
  calc
    _ = AdjacentCollapse.collapse (picked.map (outerWord k)).flatten := hc
    _ = outerWord k picked.flatten := collapse_outer_picked k picked
    _ = outerWord k out := by rw [ho]

end SerrePositivity.EInfinity.Surjection.CompositeRecovery
