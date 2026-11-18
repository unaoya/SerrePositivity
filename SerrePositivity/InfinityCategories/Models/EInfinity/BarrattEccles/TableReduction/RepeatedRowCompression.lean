module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.RowFusionCollapse

/-!
模型。文献の定義との比較は後で
# 同じ隣接行を全て融合した抽出表

概要：Berger–Fresse §1.5.8 の逆構成で外側置換の連続する繰り返しを除く。
方針：後続を先に圧縮し、先頭の行が同じなら行長を r+s−1 に融合する。
規約：元の行の非重複性を要求するが、出力語の非退化性は要求しない。
使われ方：復元外側表を元の外側置換列の行数へ戻す。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse

variable {α : Type*} [DecidableEq α]

/-- 概要：同じ隣接行を共有文字一つの融合で圧縮した表（BF §1.5.8）。
方針：後続の圧縮の先頭と元の先頭を比較し、同じ行だけを融合する。
規約：異なる行の順序は保つ。
使われ方：shuffle 経路由来の外側の重複行を除く実際の表。 -/
def compressRows : List (List α × ℕ) → List (List α × ℕ)
  | [] => []
  | p :: rows =>
    match compressRows rows with
    | [] => [p]
    | q :: rest => if p.1 = q.1 then (p.1, p.2 + q.2 - 1) :: rest else p :: q :: rest

/-- 概要：圧縮表の行列は元の行列の連続重複縮約（BF §1.5.8）。
方針：後続行列の縮約と先頭比較の分岐を同期する。
規約：行長の正値性や成功はこの行列表示には不要。
使われ方：圧縮後の外側表の行列を元の外側置換列へ同定する。 -/
lemma compressRows_fst (rows : List (List α × ℕ)) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.compressRows rows).map Prod.fst = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse (rows.map Prod.fst) := by
  induction rows with
  | nil => rfl
  | cons p rows ih =>
    cases hc : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.compressRows rows with
    | nil =>
      rw [hc, List.map_nil] at ih
      simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.compressRows, hc, List.map_cons, List.map_nil, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse, ← ih, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.prepend]
    | cons q rest =>
      rw [hc, List.map_cons] at ih
      simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.compressRows, hc, List.map_cons, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse, ← ih, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.prepend]
      by_cases he : p.1 = q.1 <;> simp [he]

/-- 概要：全重複行の圧縮は成功と縮約出力を保つ（BF §1.5.8）。
方針：後続の成功を圧縮し、同じ先頭二行だけを融合して縮約不変性を使う。
規約：各元の行は非重複。初期除外と元の成功出力は任意。
使われ方：実際の復元外側表から元の外側表の成功を得る。 -/
lemma compressRows_success (rows : List (List α × ℕ)) (removed out : List α)
    (hn : ∀ p ∈ rows, p.1.Nodup) (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows rows removed = some out) :
    ∃ out', _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.compressRows rows) removed = some out' ∧
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse out' = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse out := by
  induction rows generalizing removed out with
  | nil => exact ⟨out, h, rfl⟩
  | cons p rows ih =>
    obtain ⟨hr, hb, tail, ht, ho⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_cons_success _ _ _ _ _ h
    obtain ⟨tail', ht', he⟩ := ih _ _ (fun q hq => hn q (List.mem_cons_of_mem p hq)) ht
    have hs := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_cons_of_success p.1 p.2 (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.compressRows rows) removed tail' hr hb ht'
    have hw : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed p.1).take p.2 ++ tail') = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse out := by
      rw [ho]
      exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse_append_congr _ _ _ he
    cases hc : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.compressRows rows with
    | nil =>
      refine ⟨_, ?_, hw⟩
      simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.compressRows, hc] using hs
    | cons q rest =>
      by_cases hq : p.1 = q.1
      · have hs' : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows ((p.1, p.2) :: (p.1, q.2) :: rest) removed =
            some ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed p.1).take p.2 ++ tail') := by
          have hpair : q = (p.1, q.2) := Prod.ext hq.symm rfl
          rw [hc, hpair] at hs
          exact hs
        obtain ⟨out', hf, hh⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rowFusion_collapse removed p.1 (hn p List.mem_cons_self)
          p.2 q.2 rest _ hs'
        refine ⟨out', ?_, hh.trans hw⟩
        simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.compressRows, hc, ite_eq_left hq] using hf
      · refine ⟨_, ?_, hw⟩
        simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.compressRows, hc, ite_eq_right hq] using hs

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
