module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordInsertBetween

/-!
# 中央一列挿入の元の列の像

概要：元の挿入単射の像は、追加した一列だけを除いた元の列の集合。
方針：左右の埋め込みの自然数の値から全ての前像を明示する。
規約：色と順序を保つ同じ元の単射を使う。
使われ方：元の eraseInclusion との厳密な因子分解。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

lemma insertBetween_range (a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction) :
    Set.range (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.insertBetween a b d).orderHom = {_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.insertedColumn a b d}ᶜ := by
  ext j
  simp only [Set.mem_range, Set.mem_compl_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.insertBetween_ne_inserted a b d i
  · intro hj
    have hne : j.val ≠ a.length := by
      intro h
      apply hj
      apply Fin.ext
      simpa [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.insertedColumn] using h
    have hjlt : j.val < a.length + 1 + b.length := j.isLt
    by_cases h : j.val < a.length
    · let i : Fin a.length := ⟨j.val, h⟩
      refine ⟨i.castAdd b.length, ?_⟩
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.insertBetween_left]
      rfl
    · let i : Fin b.length := ⟨j.val - (a.length + 1), by omega⟩
      refine ⟨i.natAdd a.length, ?_⟩
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.insertBetween_right]
      apply Fin.ext
      change a.length + 1 + (j.val - (a.length + 1)) = j.val
      omega

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (insertBetween_range)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
