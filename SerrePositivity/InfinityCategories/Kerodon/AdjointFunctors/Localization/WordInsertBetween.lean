module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppendIndices
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordEmptyFiber

/-!
# 二つの語の間への一列挿入

概要：元の二つの語の列を保ち、接合点に一列だけ恒等列を挿入する元の語の単射。
方針：左右の列を有限順序の直和で埋め込み、追加列だけを像から外す。
規約：向き・順序・元の全列を保持する。空語も含む。
使われ方：中央 backward 恒等列の挿入関手。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable (a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction)

def insertBetween : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a b ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single d)) b where
  orderHom :=
    { toFun := Fin.addCases (fun i => (i.castAdd 1).castAdd b.length)
        (fun i => i.natAdd (a.length + 1))
      monotone' := by
        intro i j hij
        cases i using Fin.addCases with
        | left i =>
          cases j using Fin.addCases with
          | left j =>
            simp only [Fin.addCases_left]
            exact hij
          | right j =>
            simp only [Fin.addCases_left, Fin.addCases_right]
            change i.val ≤ a.length + 1 + j.val
            have := i.isLt
            omega
        | right i =>
          cases j using Fin.addCases with
          | left j =>
            have := j.isLt
            change a.length + i.val ≤ j.val at hij
            omega
          | right j =>
            simp only [Fin.addCases_right]
            change a.length + i.val ≤ a.length + j.val at hij
            change a.length + 1 + i.val ≤ a.length + 1 + j.val
            omega }
  direction_eq i := by
    cases i using Fin.addCases with
    | left i =>
      change Fin.addCases (motive := fun _ => _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction)
        (Fin.addCases a.direction (fun _ : Fin 1 => d)) b.direction
        (Fin.addCases (motive := fun _ => Fin (a.length + 1 + b.length))
          (fun k => (k.castAdd 1).castAdd b.length) (fun k => k.natAdd (a.length + 1))
          (i.castAdd b.length)) = Fin.addCases a.direction b.direction (i.castAdd b.length)
      simp only [Fin.addCases_left]
    | right i =>
      change Fin.addCases (motive := fun _ => _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction)
        (Fin.addCases a.direction (fun _ : Fin 1 => d)) b.direction
        (Fin.addCases (motive := fun _ => Fin (a.length + 1 + b.length))
          (fun k => (k.castAdd 1).castAdd b.length) (fun k => k.natAdd (a.length + 1))
          (i.natAdd a.length)) = Fin.addCases a.direction b.direction (i.natAdd a.length)
      simp only [Fin.addCases_right]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (insertBetween)


lemma insertBetween_left (i : Fin a.length) :
    (insertBetween a b d).orderHom (i.castAdd b.length) = (i.castAdd 1).castAdd b.length := by
  change Fin.addCases (motive := fun _ => Fin (a.length + 1 + b.length))
    (fun k => (k.castAdd 1).castAdd b.length) (fun k => k.natAdd (a.length + 1))
    (i.castAdd b.length) = _
  exact Fin.addCases_left i

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (insertBetween_left)


lemma insertBetween_right (i : Fin b.length) :
    (insertBetween a b d).orderHom (i.natAdd a.length) = i.natAdd (a.length + 1) := by
  change Fin.addCases (motive := fun _ => Fin (a.length + 1 + b.length))
    (fun k => (k.castAdd 1).castAdd b.length) (fun k => k.natAdd (a.length + 1))
    (i.natAdd a.length) = _
  exact Fin.addCases_right i

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (insertBetween_right)


def insertedColumn : Fin (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single d)) b).length :=
  ((0 : Fin 1).natAdd a.length).castAdd b.length

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (insertedColumn)


lemma insertBetween_injective : Function.Injective (insertBetween a b d).orderHom := by
  intro i j h
  have hv := congrArg Fin.val h
  cases i using Fin.addCases with
  | left i =>
    cases j using Fin.addCases with
    | left j =>
      apply congrArg (fun i : Fin a.length => i.castAdd b.length)
      apply Fin.ext
      rw [insertBetween_left, insertBetween_left] at hv
      exact hv
    | right j =>
      rw [insertBetween_left, insertBetween_right] at hv
      have := i.isLt
      change i.val = a.length + 1 + j.val at hv
      omega
  | right i =>
    cases j using Fin.addCases with
    | left j =>
      rw [insertBetween_left, insertBetween_right] at hv
      have := j.isLt
      change a.length + 1 + i.val = j.val at hv
      omega
    | right j =>
      apply congrArg (fun i : Fin b.length => i.natAdd a.length)
      apply Fin.ext
      rw [insertBetween_right, insertBetween_right] at hv
      change a.length + 1 + i.val = a.length + 1 + j.val at hv
      omega

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (insertBetween_injective)


lemma insertBetween_ne_inserted (i : Fin (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a b).length) :
    (insertBetween a b d).orderHom i ≠ insertedColumn a b d := by
  intro h
  have hv := congrArg Fin.val h
  cases i using Fin.addCases with
  | left i =>
    rw [insertBetween_left] at hv
    change i.val = a.length + 0 at hv
    have := i.isLt
    omega
  | right i =>
    rw [insertBetween_right] at hv
    change a.length + 1 + i.val = a.length + 0 at hv
    omega

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (insertBetween_ne_inserted)


lemma insertBetween_cut_inserted :
    (insertBetween a b d).cut (insertedColumn a b d).castSucc =
      (insertBetween a b d).cut (insertedColumn a b d).succ :=
  (insertBetween a b d).cut_empty_fiber _ (insertBetween_ne_inserted a b d)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (insertBetween_cut_inserted)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
