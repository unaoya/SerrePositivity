module

public import SerrePositivity.EInfinity.Hammock.WordInsertBetween

/-!
# 中央一列挿入の元の列の像

概要：元の挿入単射の像は、追加した一列だけを除いた元の列の集合。
方針：左右の埋め込みの自然数の値から全ての前像を明示する。
規約：色と順序を保つ同じ元の単射を使う。
使われ方：元の eraseInclusion との厳密な因子分解。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.Word
open CategoryTheory

lemma insertBetween_range (a b : Word) (d : Direction) :
    Set.range (insertBetween a b d).orderHom = {insertedColumn a b d}ᶜ := by
  ext j
  simp only [Set.mem_range, Set.mem_compl_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    exact insertBetween_ne_inserted a b d i
  · intro hj
    have hne : j.val ≠ a.length := by
      intro h
      apply hj
      apply Fin.ext
      simpa [insertedColumn] using h
    have hjlt : j.val < a.length + 1 + b.length := j.isLt
    by_cases h : j.val < a.length
    · let i : Fin a.length := ⟨j.val, h⟩
      refine ⟨i.castAdd b.length, ?_⟩
      rw [insertBetween_left]
      rfl
    · let i : Fin b.length := ⟨j.val - (a.length + 1), by omega⟩
      refine ⟨i.natAdd a.length, ?_⟩
      rw [insertBetween_right]
      apply Fin.ext
      change a.length + 1 + (j.val - (a.length + 1)) = j.val
      omega

end SerrePositivity.EInfinity.Hammock.Word
