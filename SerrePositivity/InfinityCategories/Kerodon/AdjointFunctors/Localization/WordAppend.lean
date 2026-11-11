module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.CategoryTheory.Products.Basic
public import Lean.Elab.Tactic.Omega

/-!
# Hammock の語の連結関手

概要：二つの向き付き語の連結を、全ての色を保つ単調写像にも作用させる。
方針：左の列と右の列の番号を有限順序の直和で連結する。
規約：語の並びは左から右。両部分の全列の向きを保持する。
使われ方：固定語の graph の合成と全語の余極限上の合成。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend
open CategoryTheory

/-- 元の順序と向きを保持する語の連結。 -/
abbrev append (a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word :=
  ⟨a.length + b.length, Fin.addCases (motive := fun _ => _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction) a.direction b.direction⟩

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend (append)


@[simp] lemma append_direction_left (a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (i : Fin a.length) :
    (append a b).direction (i.castAdd b.length) = a.direction i := by
  simp only [Fin.addCases_left]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend (append_direction_left)


@[simp] lemma append_direction_right (a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (i : Fin b.length) :
    (append a b).direction (i.natAdd a.length) = b.direction i := by
  simp only [Fin.addCases_right]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend (append_direction_right)


/-- 二つの元の語の写像の連結。 -/
def appendMap {a b a' b' : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (f : a ⟶ a') (g : b ⟶ b') : append a b ⟶ append a' b' where
  orderHom :=
    { toFun := Fin.addCases (fun i => (f.orderHom i).castAdd b'.length)
        (fun i => (g.orderHom i).natAdd a'.length)
      monotone' := by
        intro i j hij
        cases i using Fin.addCases with
        | left i =>
          cases j using Fin.addCases with
          | left j =>
            simp only [Fin.addCases_left]
            exact f.orderHom.monotone hij
          | right j =>
            simp only [Fin.addCases_left, Fin.addCases_right]
            change (f.orderHom i).val ≤ a'.length + (g.orderHom j).val
            have := (f.orderHom i).isLt
            omega
        | right i =>
          cases j using Fin.addCases with
          | left j =>
            have := j.isLt
            change a.length + i.val ≤ j.val at hij
            omega
          | right j =>
            simp only [Fin.addCases_right]
            have hi : i ≤ j := by change a.length + i.val ≤ a.length + j.val at hij; omega
            exact Nat.add_le_add_left (g.orderHom.monotone hi) _ }
  direction_eq i := by
    cases i using Fin.addCases with
    | left i =>
      change Fin.addCases (motive := fun _ => _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction) a'.direction b'.direction
        (Fin.addCases (motive := fun _ => Fin (a'.length + b'.length))
          (fun k => (f.orderHom k).castAdd b'.length)
          (fun k => (g.orderHom k).natAdd a'.length) (i.castAdd b.length)) =
          Fin.addCases (motive := fun _ => _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction) a.direction b.direction (i.castAdd b.length)
      simp only [Fin.addCases_left]
      exact f.direction_eq i
    | right i =>
      change Fin.addCases (motive := fun _ => _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction) a'.direction b'.direction
        (Fin.addCases (motive := fun _ => Fin (a'.length + b'.length))
          (fun k => (f.orderHom k).castAdd b'.length)
          (fun k => (g.orderHom k).natAdd a'.length) (i.natAdd a.length)) =
          Fin.addCases (motive := fun _ => _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction) a.direction b.direction (i.natAdd a.length)
      simp only [Fin.addCases_right]
      exact g.direction_eq i

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend (appendMap)


@[simp] lemma appendMap_left {a b a' b' : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (f : a ⟶ a') (g : b ⟶ b') (i : Fin a.length) :
    (appendMap f g).orderHom (i.castAdd b.length) = (f.orderHom i).castAdd b'.length :=
  by
    change Fin.addCases (motive := fun _ => Fin (a'.length + b'.length))
          (fun k => (f.orderHom k).castAdd b'.length)
      (fun k => (g.orderHom k).natAdd a'.length) (i.castAdd b.length) =
        (f.orderHom i).castAdd b'.length
    exact Fin.addCases_left i

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend (appendMap_left)


@[simp] lemma appendMap_right {a b a' b' : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (f : a ⟶ a') (g : b ⟶ b') (i : Fin b.length) :
    (appendMap f g).orderHom (i.natAdd a.length) = (g.orderHom i).natAdd a'.length :=
  by
    change Fin.addCases (motive := fun _ => Fin (a'.length + b'.length))
          (fun k => (f.orderHom k).castAdd b'.length)
      (fun k => (g.orderHom k).natAdd a'.length) (i.natAdd a.length) =
        (g.orderHom i).natAdd a'.length
    exact Fin.addCases_right i

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend (appendMap_right)


@[simp] lemma appendMap_id (a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) : appendMap (𝟙 a) (𝟙 b) = 𝟙 (append a b) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.hom_ext
  intro i
  cases i using Fin.addCases with
  | left i => exact appendMap_left (𝟙 a) (𝟙 b) i
  | right i => exact appendMap_right (𝟙 a) (𝟙 b) i

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend (appendMap_id)


lemma appendMap_comp {a b a' b' a'' b'' : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word}
    (f : a ⟶ a') (g : b ⟶ b') (f' : a' ⟶ a'') (g' : b' ⟶ b'') :
    appendMap (f ≫ f') (g ≫ g') = appendMap f g ≫ appendMap f' g' := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.hom_ext
  intro i
  cases i using Fin.addCases with
  | left i =>
    change (appendMap (f ≫ f') (g ≫ g')).orderHom (i.castAdd b.length) =
      (appendMap f' g').orderHom ((appendMap f g).orderHom (i.castAdd b.length))
    rw [appendMap_left (f ≫ f') (g ≫ g') i, appendMap_left f g i,
      appendMap_left f' g' (f.orderHom i)]
    rfl
  | right i =>
    change (appendMap (f ≫ f') (g ≫ g')).orderHom (i.natAdd a.length) =
      (appendMap f' g').orderHom ((appendMap f g).orderHom (i.natAdd a.length))
    rw [appendMap_right (f ≫ f') (g ≫ g') i, appendMap_right f g i,
      appendMap_right f' g' (g.orderHom i)]
    rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend (appendMap_comp)


/-- 二つの元の語の厳密な連結関手。 -/
def appendFunctor : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word × _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word where
  obj p := append p.1 p.2
  map f := appendMap f.1 f.2
  map_id p := appendMap_id p.1 p.2
  map_comp f g := appendMap_comp f.1 f.2 g.1 g.2

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend (appendFunctor)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend
