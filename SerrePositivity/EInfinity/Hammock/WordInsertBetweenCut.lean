module

public import SerrePositivity.EInfinity.Hammock.WordInsertBetween
public import SerrePositivity.EInfinity.Hammock.WordEmbeddingCut

/-!
# 中央一列挿入の切断と全位置

概要：元の左右の全頂点は同じ切断へ戻り、左右と挿入列が全位置を尽くす。
方針：元の左側の列による cut の特徴付けと有限順序の直和を使う。
規約：空の左右語も含む。長さだけによる語の同一視をしない。
使われ方：元の語の作用と、中央恒等列を持つ連結対象の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.Word
open CategoryTheory

variable (a b : Word) (d : Direction)

lemma insertBetween_cut_leftVertex (i : Fin (a.length + 1)) :
    (insertBetween a b d).cut
      (leftVertex (append a (single d)) b (leftVertex a (single d) i)) = leftVertex a b i := by
  apply Hom.vertex_ext
  intro k
  rw [Hom.lt_cut_iff]
  cases k using Fin.addCases with
  | left k =>
    rw [insertBetween_left]
    rfl
  | right k =>
    rw [insertBetween_right]
    change a.length + 1 + k.val < i.val ↔ a.length + k.val < i.val
    have := i.isLt
    omega

lemma insertBetween_cut_rightVertex (i : Fin (b.length + 1)) :
    (insertBetween a b d).cut (rightVertex (append a (single d)) b i) = rightVertex a b i := by
  apply Hom.vertex_ext
  intro k
  rw [Hom.lt_cut_iff]
  cases k using Fin.addCases with
  | left k =>
    rw [insertBetween_left]
    change k.val < a.length + 1 + i.val ↔ k.val < a.length + i.val
    have := k.isLt
    omega
  | right k =>
    rw [insertBetween_right]
    change a.length + 1 + k.val < a.length + 1 + i.val ↔
      a.length + k.val < a.length + i.val
    omega

lemma insertedColumn_direction :
    (append (append a (single d)) b).direction (insertedColumn a b d) = d := by
  simp [insertedColumn, append, single]

lemma insertBetween_vertex_cases
    {P : Fin ((append (append a (single d)) b).length + 1) → Prop}
    (hl : ∀ i, P (leftVertex (append a (single d)) b (leftVertex a (single d) i)))
    (hr : ∀ i, P (rightVertex (append a (single d)) b i))
    (j : Fin ((append (append a (single d)) b).length + 1)) : P j := by
  have hj : j.val < a.length + 1 + b.length + 1 := j.isLt
  by_cases h : j.val ≤ a.length
  · let i : Fin (a.length + 1) := ⟨j.val, by omega⟩
    have he : leftVertex (append a (single d)) b (leftVertex a (single d) i) = j := rfl
    exact he ▸ hl i
  · let i : Fin (b.length + 1) := ⟨j.val - (a.length + 1), by omega⟩
    have he : rightVertex (append a (single d)) b i = j := by
      apply Fin.ext
      change a.length + 1 + (j.val - (a.length + 1)) = j.val
      omega
    exact he ▸ hr i

lemma insertBetween_column_cases {P : Fin (append (append a (single d)) b).length → Prop}
    (hl : ∀ i : Fin a.length, P ((i.castAdd 1).castAdd b.length))
    (hc : P (insertedColumn a b d)) (hr : ∀ i : Fin b.length, P (i.natAdd (a.length + 1)))
    (j : Fin (append (append a (single d)) b).length) : P j := by
  have hj : j.val < a.length + 1 + b.length := j.isLt
  by_cases h : j.val < a.length
  · let i : Fin a.length := ⟨j.val, h⟩
    have he : (i.castAdd 1).castAdd b.length = j := rfl
    exact he ▸ hl i
  by_cases h' : j.val = a.length
  · have he : insertedColumn a b d = j := Fin.ext (by simpa [insertedColumn] using h'.symm)
    exact he ▸ hc
  · let i : Fin b.length := ⟨j.val - (a.length + 1), by omega⟩
    have he : i.natAdd (a.length + 1) = j := by
      apply Fin.ext
      change a.length + 1 + (j.val - (a.length + 1)) = j.val
      omega
    exact he ▸ hr i

end SerrePositivity.EInfinity.Hammock.Word
