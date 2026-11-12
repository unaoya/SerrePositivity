module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordUnit
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Fin
public import Lean.Elab.Tactic.Omega

/-!
# 指定 backward 列の両隣の backward 列

概要：前後に backward 列が存在するとき、最も近い二列の間は forward だけになる。
方針：元の列番号の有限集合の最大元・最小元を選ぶ。
規約：元の番号と向きを保持し、間の forward 区間は長さ零でもよい。
使われ方：padding された任意の語の中央列を既存の局所形へ分解する。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization

structure BackwardBounds (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (p : Fin w.length) where
  left : Fin w.length
  right : Fin w.length
  left_lt : left < p
  lt_right : p < right
  left_backward : w.direction left = .backward
  middle_backward : w.direction p = .backward
  right_backward : w.direction right = .backward
  left_forward : ∀ i, left < i → i < p → w.direction i = .forward
  right_forward : ∀ i, p < i → i < right → w.direction i = .forward

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (BackwardBounds)


lemma exists_backwardBounds (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (p : Fin w.length) (hp : w.direction p = .backward)
    (hl : ∃ i, i < p ∧ w.direction i = .backward)
    (hr : ∃ i, p < i ∧ w.direction i = .backward) : Nonempty (BackwardBounds w p) := by
  let L := Finset.univ.filter (fun i => i < p ∧ w.direction i = .backward)
  let R := Finset.univ.filter (fun i => p < i ∧ w.direction i = .backward)
  have hL : L.Nonempty := by
    obtain ⟨i, hi⟩ := hl
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  have hR : R.Nonempty := by
    obtain ⟨i, hi⟩ := hr
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  have hleft := (Finset.mem_filter.mp (Finset.max'_mem L hL)).2
  have hright := (Finset.mem_filter.mp (Finset.min'_mem R hR)).2
  refine ⟨⟨L.max' hL, R.min' hR, hleft.1, hright.1, hleft.2, hp, hright.2, ?_, ?_⟩⟩
  · intro i hi hip
    have hnot : w.direction i ≠ .backward := by
      intro hd
      have hm : i ∈ L := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hip, hd⟩
      exact (not_le_of_gt hi) (Finset.le_max' L i hm)
    cases hd : w.direction i with
    | forward => rfl
    | backward => exact False.elim (hnot hd)
  · intro i hpi hi
    have hnot : w.direction i ≠ .backward := by
      intro hd
      have hm : i ∈ R := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpi, hd⟩
      exact (not_le_of_gt hi) (Finset.min'_le R i hm)
    cases hd : w.direction i with
    | forward => rfl
    | backward => exact False.elim (hnot hd)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (exists_backwardBounds)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
