module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.FilterMapTrace
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.RecurrentEnds
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.NullaryErasure

/-!
模型。文献の定義との比較は後で
# 一出現の指定値削除が保つ行末と非空選択

概要：Berger–Fresse §1.5.7–9 の元の成功表を空語合成へ射影する条件を証明する。
方針：非最終行末は再出現するため一出現の指定値ではなく、その文字が後続も非空にする。
規約：出力の指定値は高々一回、削除後の全出力は非空。
使われ方：元の成功表の全行を捨てずに nullary 合成表の成功へ移す。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：一出現以下の指定値の削除は非最終行末と全行の非空性を保つ（BF §1.5.7–9）。
方針：再出現する行末が指定値なら二出現となる矛盾を使い、後続へ帰納する。
規約：最終行末は消してよい。削除後の全語は非空。
使われ方：全抽出の部分射影の保持条件を元の成功表から導く。 -/
lemma recurrentEnds_eraseSlotWord_ready {m : ℕ} (k : Fin (m + 1))
    (picked : List (List (Fin (m + 1)))) (hr : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.RecurrentEnds picked)
    (hne : ∀ row ∈ picked, row ≠ []) (hc : picked.flatten.count k ≤ 1)
    (ho : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.eraseSlotWord k picked.flatten ≠ []) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.FilterMapReady (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.eraseSlotLabel k) picked := by
  induction picked with
  | nil => trivial
  | cons word rest ih =>
    have hw : word ≠ [] := hne word List.mem_cons_self
    by_cases he : rest = []
    · subst rest
      exact ⟨by simpa only [List.flatten_cons, List.flatten_nil, List.append_nil,
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.eraseSlotWord] using ho, fun h => False.elim (h rfl), trivial⟩
    · let a := word.getLast hw
      have hlast : word.getLast? = some a := List.getLast?_eq_some_getLast hw
      have ha : a ∈ word := List.mem_of_mem_getLast? hlast
      have ht : a ∈ rest.flatten := hr.1 hw he
      have hak : a ≠ k := by
        intro hk
        have hp : 0 < word.count k := List.count_pos_iff.mpr (hk ▸ ha)
        have hq : 0 < rest.flatten.count k := List.count_pos_iff.mpr (hk ▸ ht)
        simp only [List.flatten_cons, List.count_append] at hc
        omega
      let b := _root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition m 0 k ⟨a, hak⟩
      have hf : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.eraseSlotLabel k a = some b := by
        simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.eraseSlotLabel, dite_eq_right hak]
        rfl
      have hword : word.filterMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.eraseSlotLabel k) ≠ [] := by
        intro hz
        have hm := List.mem_filterMap.mpr ⟨a, ha, hf⟩
        rw [hz] at hm
        exact List.not_mem_nil hm
      have htail : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.eraseSlotWord k rest.flatten ≠ [] := by
        intro hz
        have hm := List.mem_filterMap.mpr ⟨a, ht, hf⟩
        change b ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.eraseSlotWord k rest.flatten at hm
        rw [hz] at hm
        exact List.not_mem_nil hm
      have hcount : rest.flatten.count k ≤ 1 := by
        simp only [List.flatten_cons, List.count_append] at hc
        omega
      exact ⟨hword, fun _ => ⟨a, b, hlast, hf⟩,
        ih hr.2 (fun row hm => hne row (List.mem_cons_of_mem _ hm)) hcount htail⟩

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
