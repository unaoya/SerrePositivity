module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.TwoRowSplit
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleOffsets

/-!
模型。文献の定義との比較は後で
# 分割された二行を通る元の成功抽出

概要：Berger–Fresse §1.4.4 の三部分の比較に渡す元の状態と出力を取り出す。
方針：受け取り行の前と中間行の後で抽出を切り、一行の成功条件を開く。
規約：元の行リストの分割だけを入力とし、出力の非退化性は要求しない。
使われ方：実際の Schedule から行長移動の全局所入力を構成する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

variable {α : Type*} [DecidableEq α]

/-- 概要：二つの指定行を通る成功抽出の全ての境界状態（BF §1.4.4）。
方針：先行部分と中間部分の抽出証跡、二行の成功条件、後続抽出を順に分ける。
規約：受け取り行と削除行の行長はまだ任意の正の値。
使われ方：前・受け取り行・中・削除行・後の出力と状態を同時に保持する。 -/
lemma two_row_extraction (before middle after : List (List α × ℕ))
    (receiver donor : List α) (r s : ℕ) (initial out : List α)
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (before ++ (receiver, r) :: (middle ++ (donor, s) :: after)) initial =
      some out) :
    ∃ selectedBefore removed picked finish tail,
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix before initial selectedBefore removed ∧
      0 < r ∧ r ≤ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed receiver).length ∧
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix middle (removed ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed receiver).take (r - 1))
        picked finish ∧
      0 < s ∧ s ≤ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available finish donor).length ∧
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows after (finish ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available finish donor).take (s - 1)) = some tail ∧
      out = selectedBefore.flatten ++ ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed receiver).take r ++
        (picked.flatten ++ ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available finish donor).take s ++ tail))) := by
  obtain ⟨selectedBefore, removed, restOut, hp, hrest, hout⟩ :=
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.extractionPrefix_of_reduceRows before _ initial out h
  obtain ⟨hr, hb, midOut, hm, hrec⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_cons_success _ _ _ _ _ hrest
  obtain ⟨picked, finish, donorOut, hmid, hdonor, hmiddle⟩ :=
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.extractionPrefix_of_reduceRows middle _ _ midOut hm
  obtain ⟨hs, hd, tail, ht, hdonorOut⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_cons_success _ _ _ _ _ hdonor
  refine ⟨selectedBefore, removed, picked, finish, tail, hp, hr, hb, hmid, hs, hd, ht, ?_⟩
  rw [hout, hrec, hmiddle, hdonorOut]

/-- 概要：二行の分割の先行行長の和は指定行の開始位置（BF §1.4.4）。
方針：実際の行リストの先頭部分を取り、その長さの和を評価する。
規約：分割された先行部分の長さと行番号が一致する。
使われ方：抽出された出力の先行部分の長さを Schedule の位置へ直す。 -/
lemma rows_prefix_sum {n d : ℕ} (w : Fin (d + 1) → Equiv.Perm (Fin n))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d) (before rest : List (List (Fin n) × ℕ))
    (he : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r = before ++ rest) (i : Fin (d + 1)) (hi : before.length = i.val) :
    (before.map Prod.snd).sum = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r i := by
  have ht : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r).take before.length = before := by rw [he]; simp
  have hm : before.map Prod.snd =
      (List.ofFn (fun j => (r.val j).val)).take before.length := by
    calc
      _ = ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r).take before.length).map Prod.snd := by rw [ht]
      _ = ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r).map Prod.snd).take before.length := List.map_take
      _ = _ := by rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows, List.map_ofFn]; rfl
  simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset, hi] using congrArg List.sum hm

/-- 概要：抽出証跡の出力長は先行行長の総和（BF §1.4.4）。
方針：行長リストの証明書を総和で評価する。
規約：元の除外状態と終端の状態には依存しない。
使われ方：二行で切り出した出力の区間を Schedule の行開始位置と同定する。 -/
lemma _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix.output_length {before : List (List α × ℕ)}
    {removed finish : List α} {picked : List (List α)}
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix before removed picked finish) :
    picked.flatten.length = (before.map Prod.snd).sum := by
  simpa only [List.length_flatten] using congrArg List.sum h.lengths

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
