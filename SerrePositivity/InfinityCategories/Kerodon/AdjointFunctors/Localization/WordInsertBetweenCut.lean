module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordInsertBetween
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordEmbeddingCut

/-!
# 中央一列挿入の切断と全位置

概要：元の左右の全頂点は同じ切断へ戻り、左右と挿入列が全位置を尽くす。
方針：元の左側の列による cut の特徴付けと有限順序の直和を使う。
規約：空の左右語も含む。長さだけによる語の同一視をしない。
使われ方：元の語の作用と、中央恒等列を持つ連結対象の照合。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable (a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction)

lemma insertBetween_cut_leftVertex (i : Fin (a.length + 1)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.insertBetween a b d).cut
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single d)) b (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftVertex a (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single d) i)) = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftVertex a b i := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Hom.vertex_ext
  intro k
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Hom.lt_cut_iff]
  cases k using Fin.addCases with
  | left k =>
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.insertBetween_left]
    rfl
  | right k =>
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.insertBetween_right]
    change a.length + 1 + k.val < i.val ↔ a.length + k.val < i.val
    have := i.isLt
    omega

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (insertBetween_cut_leftVertex)


lemma insertBetween_cut_rightVertex (i : Fin (b.length + 1)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.insertBetween a b d).cut (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single d)) b i) = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightVertex a b i := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Hom.vertex_ext
  intro k
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Hom.lt_cut_iff]
  cases k using Fin.addCases with
  | left k =>
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.insertBetween_left]
    change k.val < a.length + 1 + i.val ↔ k.val < a.length + i.val
    have := k.isLt
    omega
  | right k =>
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.insertBetween_right]
    change a.length + 1 + k.val < a.length + 1 + i.val ↔
      a.length + k.val < a.length + i.val
    omega

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (insertBetween_cut_rightVertex)


lemma insertedColumn_direction :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single d)) b).direction (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.insertedColumn a b d) = d := by
  simp [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.insertedColumn, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (insertedColumn_direction)


lemma insertBetween_vertex_cases
    {P : Fin ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single d)) b).length + 1) → Prop}
    (hl : ∀ i, P (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single d)) b (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftVertex a (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single d) i)))
    (hr : ∀ i, P (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single d)) b i))
    (j : Fin ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single d)) b).length + 1)) : P j := by
  have hj : j.val < a.length + 1 + b.length + 1 := j.isLt
  by_cases h : j.val ≤ a.length
  · let i : Fin (a.length + 1) := ⟨j.val, by omega⟩
    have he : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single d)) b (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftVertex a (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single d) i) = j := rfl
    exact he ▸ hl i
  · let i : Fin (b.length + 1) := ⟨j.val - (a.length + 1), by omega⟩
    have he : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single d)) b i = j := by
      apply Fin.ext
      change a.length + 1 + (j.val - (a.length + 1)) = j.val
      omega
    exact he ▸ hr i

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (insertBetween_vertex_cases)


lemma insertBetween_column_cases {P : Fin (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single d)) b).length → Prop}
    (hl : ∀ i : Fin a.length, P ((i.castAdd 1).castAdd b.length))
    (hc : P (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.insertedColumn a b d)) (hr : ∀ i : Fin b.length, P (i.natAdd (a.length + 1)))
    (j : Fin (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single d)) b).length) : P j := by
  have hj : j.val < a.length + 1 + b.length := j.isLt
  by_cases h : j.val < a.length
  · let i : Fin a.length := ⟨j.val, h⟩
    have he : (i.castAdd 1).castAdd b.length = j := rfl
    exact he ▸ hl i
  by_cases h' : j.val = a.length
  · have he : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.insertedColumn a b d = j := Fin.ext (by simpa [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.insertedColumn] using h'.symm)
    exact he ▸ hc
  · let i : Fin b.length := ⟨j.val - (a.length + 1), by omega⟩
    have he : i.natAdd (a.length + 1) = j := by
      apply Fin.ext
      change a.length + 1 + (j.val - (a.length + 1)) = j.val
      omega
    exact he ▸ hr i

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (insertBetween_column_cases)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
