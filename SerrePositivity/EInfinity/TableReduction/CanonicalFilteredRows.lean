module

public import SerrePositivity.EInfinity.TableReduction.CanonicalAdjacentVertices
public import SerrePositivity.EInfinity.TableReduction.FinalSegments

/-!
# 正しい先行除外の後の標準行

概要：Berger–Fresse §1.4.3 の正しい行長に沿って進む table の状態を計算する。
方針：開始位置までに確定した値を除き、行内の最終出現部分と移動する文字を残す。
規約：除外リストは pastFinals、行末は対応する caesuraAt。
使われ方：標準頂点列に対する境界による行長の強制を適用する。
-/

@[expose] public section

namespace SerrePositivity.EInfinity.TableReduction

open Surjection

/-- 概要：行末の確定済み部分は行開始時の部分と行内の最終出現の連結（BF §1.4.3）。
方針：行内部に区切りがないことを区間の除外更新の式へ渡す。
規約：区切りの文字自体は新しく確定した部分に含めない。
使われ方：除外後に残る行内の文字列を特定する。 -/
lemma pastFinals_cut_eq_start_append {n d : ℕ} (v : BasisWord n d) (i : Fin d) :
    pastFinals (List.ofFn v.val) (caesuraAt v i).val =
      pastFinals (List.ofFn v.val) (rowStart v i.castSucc) ++
        ((List.ofFn v.val).drop (rowStart v i.castSucc)).take
          ((caesuraAt v i).val - rowStart v i.castSucc) := by
  apply pastFinals_eq_append_segment _ _ _ (rowStart_le_caesuraAt v i)
    (by simp only [List.length_ofFn]; exact Nat.le_of_lt (caesuraAt v i).isLt)
  intro k hk hstart hcut
  have hk' : k < n + d := by simpa only [List.length_ofFn] using hk
  have hnc := not_caesura_between_start_and_cut v i ⟨k, hk'⟩ hstart hcut
  simpa only [List.getElem_ofFn] using
    (caesura_iff_mem_drop v.val ⟨k, hk'⟩).not.mp hnc

/-- 概要：標準行の除外後の共通先頭となる最終出現部分（BF §1.4.3）。
方針：開始位置から区切り直前までの元の文字列を取る。
規約：長さ零の先頭も許す。
使われ方：正しい行長はこの部分の長さに 1 を加えたもの。 -/
def finalSegment {n d : ℕ} (v : BasisWord n d) (i : Fin d) : List (Fin n) :=
  ((List.ofFn v.val).drop (rowStart v i.castSucc)).take
    ((caesuraAt v i).val - rowStart v i.castSucc)

/-- 概要：最終出現部分の長さは区切りと開始位置の差（BF §1.4.3）。
方針：区切りが元の語の範囲内であることから take の長さを計算する。
規約：差は自然数の差。
使われ方：境界から得られる行長を元の語の行長へ戻す。 -/
lemma finalSegment_length {n d : ℕ} (v : BasisWord n d) (i : Fin d) :
    (finalSegment v i).length = (caesuraAt v i).val - rowStart v i.castSucc := by
  simp only [finalSegment, List.length_take, List.length_drop, List.length_ofFn]
  apply Nat.min_eq_left
  have hc := (caesuraAt v i).isLt
  omega

/-- 概要：現在行から先行の確定値を除くと行内の部分と後続の列が残る（BF §1.4.3）。
方針：行開始と区切りの同じ復元行を使い、既知の先頭を重複のない行から除く。
規約：先行除外は実際の pastFinals とする。
使われ方：境界による行長の強制の第一の行を供給する。 -/
lemma available_canonicalRow_start {n d : ℕ} (v : BasisWord n d) (i : Fin d) :
    available (pastFinals (List.ofFn v.val) (rowStart v i.castSucc))
      (canonicalRow (List.ofFn v.val) (rowStart v i.castSucc)) =
        finalSegment v i ++ firstOccurrences ((List.ofFn v.val).drop (caesuraAt v i).val) := by
  rw [canonicalRow_start_eq_cut]
  have hn := canonicalRow_nodup (List.ofFn v.val) (caesuraAt v i).val
  rw [canonicalRow, pastFinals_cut_eq_start_append, List.append_assoc] at hn ⊢
  exact available_prefix_of_nodup _ _ hn

/-- 概要：次行から同じ先行除外を除くと移動後の文字列が残る（BF §1.4.3）。
方針：区切りの通過では確定前半が変わらないことを使う。
規約：次行自身の抽出に先立つ状態を計算する。
使われ方：境界による行長の強制の第二の行を供給する。 -/
lemma available_canonicalRow_next {n d : ℕ} (v : BasisWord n d) (i : Fin d) :
    available (pastFinals (List.ofFn v.val) (rowStart v i.castSucc))
      (canonicalRow (List.ofFn v.val) (rowStart v i.succ)) =
        finalSegment v i ++
          firstOccurrences ((List.ofFn v.val).drop ((caesuraAt v i).val + 1)) := by
  rw [rowStart_succ_eq_caesuraAt]
  have hp : (caesuraAt v i).val < (List.ofFn v.val).length := by
    simpa only [List.length_ofFn] using (caesuraAt v i).isLt
  have ha : (List.ofFn v.val)[(caesuraAt v i).val] ∈
      (List.ofFn v.val).drop ((caesuraAt v i).val + 1) := by
    simpa only [List.getElem_ofFn, Fin.eta] using
      (caesura_iff_mem_drop v.val (caesuraAt v i)).mp (caesuraAt_caesura v i)
  have hn := canonicalRow_nodup (List.ofFn v.val) ((caesuraAt v i).val + 1)
  rw [canonicalRow_after_step_of_mem _ _ hp ha,
    pastFinals_cut_eq_start_append, List.append_assoc] at hn ⊢
  exact available_prefix_of_nodup _ _ hn

end SerrePositivity.EInfinity.TableReduction
