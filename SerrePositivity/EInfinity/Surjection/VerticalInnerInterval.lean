module

public import SerrePositivity.EInfinity.Surjection.VerticalInnerFinal
public import SerrePositivity.EInfinity.Surjection.VerticalInnerPrefix

/-!
# 垂直成分全体を内側の抽出区間へ復元

概要：Berger–Fresse §1.5.8 の少なくとも一歩を持つ垂直成分の全行を射影する。
方針：先行行の終状態を保って射影し、最終行は内側末尾を残す形で接続する。
規約：最終行の内側非空性は直前の垂直行と全出力の非退化性から導く。
使われ方：合成 table の逆構成で、各垂直成分から元の内側 table の区間を作る。
-/

@[expose] public section

namespace SerrePositivity.EInfinity.Surjection

open BarrattEccles TableReduction CompositeRecovery

/-- 概要：非自明な垂直成分の最終選択語の内側射影は非空（BF §1.5.8）。
方針：先行行を帰納的に剥がし、最後の二行の実際の成功に内側先頭制約を使う。
規約：最終行以降の後続 table は任意。先行部分が一行以上あることを要求する。
使われ方：最終行の内側抽出の正の行長を元の成功だけから得る。 -/
lemma vertical_interval_final_inner_nonempty {m n : ℕ}
    (σ : Equiv.Perm (Fin (m + 1))) (k : Fin (m + 1))
    (entries : List (Equiv.Perm (Fin n) × ℕ)) (τlast : Equiv.Perm (Fin n))
    (s : ℕ) (rest : List (List (Fin (m + n)) × ℕ))
    (removed finish tail : List (Fin (m + n))) (picked : List (List (Fin (m + n))))
    (hpre : ExtractionPrefix (verticalTable σ k entries) removed picked finish)
    (hrest : reduceRows ((List.ofFn (permutationComposition m n k σ τlast).symm, s) :: rest)
      finish = some tail) (hc : (picked.flatten ++ tail).IsChain (· ≠ ·))
    (hne : entries ≠ []) :
    ((available finish (List.ofFn (permutationComposition m n k σ τlast).symm)).take s).filterMap
      (innerLabel k) ≠ [] := by
  induction entries generalizing removed picked with
  | nil => exact (hne rfl).elim
  | cons entry entries ih =>
    obtain ⟨τ, r⟩ := entry
    have hfull := hpre.append
      ((List.ofFn (permutationComposition m n k σ τlast).symm, s) :: rest) tail hrest
    change ExtractionPrefix
      ((List.ofFn (permutationComposition m n k σ τ).symm, r) :: verticalTable σ k entries)
      removed picked finish at hpre
    cases hpre with
    | @cons _ _ _ _ picked _ hr hb ht =>
      have hc' : ((available removed
          (List.ofFn (permutationComposition m n k σ τ).symm)).take r ++
          (picked.flatten ++ tail)).IsChain (· ≠ ·) := by
        simpa only [List.flatten_cons, List.append_assoc] using hc
      cases entries with
      | nil =>
        cases ht
        exact permutationComposition_vertical_next_inner_nonempty σ τ τlast k removed _
          r s rest (by simpa only [verticalTable, List.map_cons, List.map_nil,
            List.cons_append, List.nil_append] using hfull) hc
      | cons entry entries =>
        exact ih _ _ ht hc'.right_of_append (by simp)

/-- 概要：非自明な垂直成分の全選択語を元の内側区間として抽出できる（BF §1.5.8）。
方針：非最終先行部分の射影に、非空な内側最終選択語の抽出を接続する。
規約：最後の内側文字は除外せず、後続成分との共有端点として保持する。
使われ方：任意の成功経路表から元の成功内側表を逆構成する成分。 -/
lemma vertical_interval_inner_projection {m n : ℕ}
    (σ : Equiv.Perm (Fin (m + 1))) (k : Fin (m + 1))
    (entries : List (Equiv.Perm (Fin n) × ℕ)) (τlast : Equiv.Perm (Fin n))
    (s : ℕ) (rest : List (List (Fin (m + n)) × ℕ))
    (removed finish tail : List (Fin (m + n))) (picked : List (List (Fin (m + n))))
    (hpre : ExtractionPrefix (verticalTable σ k entries) removed picked finish)
    (hrest : reduceRows ((List.ofFn (permutationComposition m n k σ τlast).symm, s) :: rest)
      finish = some tail) (hc : (picked.flatten ++ tail).IsChain (· ≠ ·))
    (hne : entries ≠ []) :
    let last := ((available finish
      (List.ofFn (permutationComposition m n k σ τlast).symm)).take s).filterMap (innerLabel k)
    ExtractionPrefix
      (filterMapRows (innerLabel k) (verticalTable σ k entries) picked ++
        [(List.ofFn τlast.symm, last.length)])
      (removed.filterMap (innerLabel k)) (picked.map (List.filterMap (innerLabel k)) ++ [last])
      (finish.filterMap (innerLabel k) ++ last.take (last.length - 1)) := by
  have hp := vertical_prefix_inner_projection σ k entries τlast s rest removed finish tail
    picked hpre hrest hc
  have hn := vertical_interval_final_inner_nonempty σ k entries τlast s rest removed finish
    tail picked hpre hrest hc hne
  have hq := permutationComposition_inner_final_step σ τlast k finish s hn
  exact hp.trans hq

end SerrePositivity.EInfinity.Surjection
