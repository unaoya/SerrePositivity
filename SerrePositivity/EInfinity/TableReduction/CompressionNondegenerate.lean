module

public import SerrePositivity.EInfinity.TableReduction.ExtractionTrace
public import SerrePositivity.EInfinity.TableReduction.RepeatedRowCompression
public import SerrePositivity.EInfinity.TableReduction.RowFusionNondegenerate
public import SerrePositivity.EInfinity.Surjection.AdjacentCollapseEndpoints

/-!
# 異なる行の境界が非退化な表の圧縮出力

概要：Berger–Fresse §1.5.8 の外側復元表で、異なる行の境界情報から圧縮出力を非退化にする。
方針：後続から帰納し、同じ行は共有文字で融合し、異なる行は境界非一致で連結する。
規約：各行は非重複。境界条件は実際の抽出証跡の選択語で指定する。
使われ方：水平境界の非一致を圧縮した外側表全体へ移す。
-/

@[expose] public section

namespace SerrePositivity.EInfinity.TableReduction

open Surjection.AdjacentCollapse

variable {α : Type*} [DecidableEq α]

/-- 概要：異なる元の行の境界で選択文字が異なるという条件（BF §1.5.8）。
方針：各行末と後続出力の先頭を再帰的に比較する。
規約：同じ行の境界には条件を課さず、共有文字の重複を許す。
使われ方：圧縮で消えない境界だけに非退化性を要求する。 -/
def SeparatedBoundaries : List (List α × ℕ) → List (List α) → Prop
  | p :: q :: rows, word :: picked =>
    (p.1 ≠ q.1 → ∀ a ∈ word.getLast?, ∀ b ∈ picked.flatten.head?, a ≠ b) ∧
      SeparatedBoundaries (q :: rows) picked
  | _, _ => True

/-- 概要：同じ行の圧縮は先頭行を保つ（BF §1.5.8）。
方針：圧縮行列の縮約表示と縮約の先頭保存を使う。
規約：空の表も none のまま。
使われ方：圧縮後の先頭が異なる場合、元の境界の非一致を使う。 -/
lemma compressRows_head (rows : List (List α × ℕ)) :
    (compressRows rows).head?.map Prod.fst = rows.head?.map Prod.fst := by
  have h := congrArg List.head? (compressRows_fst rows)
  simpa only [List.head?_map, collapse_head?] using h

/-- 概要：異なる行の境界が非退化なら全圧縮後の実際の出力も非退化（BF §1.5.8）。
方針：証跡で帰納し、同じ行の融合と異なる行の非退化な連結を分ける。
規約：境界条件は元の実際の選択語に対するもの。元の全出力の非退化性は要求しない。
使われ方：垂直境界の重複を除いて外側復元語を非退化にする。 -/
lemma ExtractionTrace.compress_isChain {rows : List (List α × ℕ)}
    {removed : List α} {picked : List (List α)} (h : ExtractionTrace rows removed picked)
    (hn : ∀ p ∈ rows, p.1.Nodup) (hsep : SeparatedBoundaries rows picked) :
    ∃ out', TableReduction.reduceRows (compressRows rows) removed = some out' ∧
      collapse out' = collapse picked.flatten ∧ out'.IsChain (· ≠ ·) := by
  induction h with
  | nil => exact ⟨[], rfl, rfl, by simp⟩
  | @cons row r rows removed picked hr hb ht ih =>
    have hsepTail : SeparatedBoundaries rows picked := by
      cases rows with
      | nil => trivial
      | cons q rows => exact hsep.2
    obtain ⟨tail', ht', he, hchain⟩ := ih
      (fun p hp => hn p (List.mem_cons_of_mem (row, r) hp)) hsepTail
    have hs := reduceRows_cons_of_success row r (compressRows rows) removed tail' hr hb ht'
    have hw : collapse ((available removed row).take r ++ tail') =
        collapse ((available removed row).take r :: picked).flatten := by
      rw [List.flatten_cons]
      exact collapse_append_congr _ _ _ he
    have hnFirst : ((available removed row).take r).IsChain (· ≠ ·) :=
      List.Pairwise.isChain ((hn (row, r) List.mem_cons_self).filter _).take
    cases hc : compressRows rows with
    | nil =>
      have hnil : tail' = [] := by
        simpa only [hc, reduceRows_nil, Option.some.injEq] using ht'.symm
      subst tail'
      refine ⟨(available removed row).take r, ?_, ?_, hnFirst⟩
      · simpa only [compressRows, hc, List.append_nil] using hs
      · simpa only [List.append_nil] using hw
    | cons q rest =>
      by_cases hq : row = q.1
      · have ht'' : TableReduction.reduceRows ((row, q.2) :: rest)
            (removed ++ (available removed row).take (r - 1)) = some tail' := by
          have hpair : q = (row, q.2) := Prod.ext hq.symm rfl
          rw [hc, hpair] at ht'
          exact ht'
        obtain ⟨out', hf, hh, hch⟩ := rowFusion_isChain_of_tail removed row
          (hn (row, r) List.mem_cons_self) r q.2 hr hb rest tail' ht'' hchain
        refine ⟨out', ?_, hh.trans hw, hch⟩
        simpa only [compressRows, hc, ite_eq_left hq] using hf
      · have hfirst := compressRows_head rows
        rw [hc] at hfirst
        cases rows with
        | nil => simp only [compressRows] at hc; cases hc
        | cons q₀ rows =>
          have hrow : q.1 = q₀.1 := by
            simpa only [List.head?_cons, Option.map_some, Option.some.injEq] using hfirst
          have hboundary := hsep.1 (fun heq => hq (heq.trans hrow.symm))
          have hhead : tail'.head? = picked.flatten.head? := by
            have h := congrArg List.head? he
            simpa only [collapse_head?] using h
          have hjoin : ((available removed row).take r ++ tail').IsChain (· ≠ ·) := by
            apply hnFirst.append hchain
            intro a ha b hb
            rw [hhead] at hb
            exact hboundary a ha b hb
          refine ⟨_, ?_, hw, hjoin⟩
          rw [compressRows, hc]
          simpa only [ite_eq_right hq, hc] using hs

end SerrePositivity.EInfinity.TableReduction
