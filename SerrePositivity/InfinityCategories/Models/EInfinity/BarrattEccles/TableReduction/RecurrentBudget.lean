module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.RecurrentEnds
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.RepeatedRowCompression
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.SingletonInsertion
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.SuccessfulRowBounds

/-!
模型。文献の定義との比較は後で
# 再出現する行末と圧縮表の行長総和

概要：Berger–Fresse §1.5.8 の復元外側表の行長−1 の総和を計算する。
方針：各非最終行末の再出現で重複除去の損失を正確に数え、同じ行の融合で総和を保つ。
規約：各元の行は非空で非重複、内部文字は後続に現れない。
使われ方：全射性と正しい行数から元の外側次数の Schedule 総和を得る。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

variable {α : Type*} [DecidableEq α]

/-- 概要：全非最終行末が再出現する分離語の長さは異なる値の個数＋行数−1（BF §1.5.8）。
方針：各行を前置した重複除去の式で、非最終末尾の一コピーだけを数える。
規約：空の全行列も許す。
使われ方：復元外側表の除外予算を全射性から計算する。 -/
lemma recurrentRows_length (picked : List (List α)) (hs : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.SeparatedRows picked)
    (hne : ∀ row ∈ picked, row ≠ []) (hr : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.RecurrentEnds picked) :
    picked.flatten.length = picked.flatten.dedup.length + (picked.length - 1) := by
  induction picked with
  | nil => simp
  | cons row rest ih =>
    have hrow := hne row List.mem_cons_self
    have hpos := List.length_pos_iff.mpr hrow
    have ht := ih hs.2.2 (fun word hw => hne word (List.mem_cons_of_mem row hw)) hr.2
    have hd := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.dedup_length_prepend_row row rest.flatten hrow hs.1 hs.2.1
    cases rest with
    | nil =>
      simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.length_cons,
        List.length_nil, Nat.add_sub_cancel, Nat.add_zero]
      exact congrArg List.length hs.1.dedup.symm
    | cons next rest =>
      have hmem := hr.1 hrow (by simp)
      simp only [hmem, ite_true] at hd
      simp only [List.flatten_cons, List.length_append, List.length_cons] at ht hd ⊢
      omega

/-- 概要：同じ隣接行の全融合は正の行長と行長−1 の総和を保つ（BF §1.5.8）。
方針：圧縮の再帰で、正の r,s の融合長 r+s−1 の余剰は両余剰の和と計算する。
規約：元の全行長が正であれば、抽出成功を仮定せず成立する。
使われ方：復元した元の外側行数から Schedule の総和を証明する。 -/
lemma compressRows_positive_excess (rows : List (List α × ℕ))
    (hp : ∀ p ∈ rows, 0 < p.2) :
    (∀ p ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.compressRows rows, 0 < p.2) ∧
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.compressRows rows).map (fun p => p.2 - 1)).sum =
        (rows.map (fun p => p.2 - 1)).sum := by
  induction rows with
  | nil => exact ⟨by simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.compressRows], rfl⟩
  | cons p rows ih =>
    obtain ⟨htpos, hte⟩ := ih (fun q hq => hp q (List.mem_cons_of_mem p hq))
    have hpos := hp p List.mem_cons_self
    cases hc : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.compressRows rows with
    | nil =>
      have hzero : (rows.map (fun p => p.2 - 1)).sum = 0 := by rw [← hte, hc]; rfl
      constructor
      · intro q hq
        have he : q = p := by simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.compressRows, hc, List.mem_singleton] using hq
        exact he ▸ hpos
      · simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.compressRows, hc, List.map_cons, List.map_nil, List.sum_cons,
          List.sum_nil, hzero, Nat.add_zero]
    | cons q rest =>
      have hqpos := htpos q (by rw [hc]; exact List.mem_cons_self)
      have hrpos (a : List α × ℕ) (ha : a ∈ rest) : 0 < a.2 :=
        htpos a (by rw [hc]; exact List.mem_cons_of_mem q ha)
      have htail : (rows.map (fun p => p.2 - 1)).sum =
          q.2 - 1 + (rest.map (fun p => p.2 - 1)).sum := by
        rw [← hte, hc, List.map_cons, List.sum_cons]
      by_cases he : p.1 = q.1
      · have hout : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.compressRows (p :: rows) = (p.1, p.2 + q.2 - 1) :: rest := by
          simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.compressRows, hc, ite_eq_left he]
        constructor
        · intro a ha
          rw [hout] at ha
          rcases List.mem_cons.mp ha with rfl | ha
          · dsimp only; omega
          · exact hrpos a ha
        · rw [hout, List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, htail]
          omega
      · have hout : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.compressRows (p :: rows) = p :: q :: rest := by
          simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.compressRows, hc, ite_eq_right he]
        constructor
        · intro a ha
          rw [hout] at ha
          rcases List.mem_cons.mp ha with rfl | ha
          · exact hpos
          · rcases List.mem_cons.mp ha with rfl | ha
            · exact hqpos
            · exact hrpos a ha
        · simp only [hout, List.map_cons, List.sum_cons, htail]

/-- 概要：再出現を持つ実際の抽出の行長−1 総和は異なる値の個数−1（BF §1.5.8）。
方針：選択語の正確な長さと正の全行長の総和の計算を合わせる。
規約：各元の行は非重複。空表では両側とも零。
使われ方：全射な外側復元語の行長総和を元の arity と次数へ合わせる。 -/
lemma _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionTrace.recurrent_excess {rows : List (List α × ℕ)} {removed : List α}
    {picked : List (List α)} (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionTrace rows removed picked)
    (hn : ∀ p ∈ rows, p.1.Nodup) (hr : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.RecurrentEnds picked) :
    (rows.map (fun p => p.2 - 1)).sum = picked.flatten.dedup.length - 1 := by
  have hlen := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.recurrentRows_length picked (h.separatedRows hn) h.nonempty hr
  have hbounds := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_row_bounds rows removed picked.flatten h.reduceRows
  have hp : ∀ x ∈ rows.map Prod.snd, 0 < x := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    exact (hbounds p hp).1
  have hsum := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.sum_sub_one_add_length (rows.map Prod.snd) hp
  simp only [List.map_map, List.length_map, Function.comp_def] at hsum
  have hout := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_length rows removed picked.flatten h.reduceRows
  rw [h.length] at hlen
  cases rows with
  | nil => cases h; rfl
  | cons p rows => simp only [List.length_cons] at hsum hlen; omega

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
