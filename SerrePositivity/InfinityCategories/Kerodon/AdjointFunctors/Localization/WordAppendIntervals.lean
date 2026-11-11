module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppendIndices

/-!
# 連結語の左右の同方向区間

概要：左右の部分の同方向区間を、連結語の同じ区間として扱う。
方針：元の列番号の直和への包含と、区間の上下界を照合する。
規約：空区間と接合点を含み、向きの条件を強めない。
使われ方：連結語での同方向区間の合成の回収。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization

lemma leftVertex_mono (a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) {p q : Fin (a.length + 1)} (hpq : p ≤ q) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftVertex a b p ≤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftVertex a b q := hpq

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (leftVertex_mono)


lemma rightVertex_mono (a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) {p q : Fin (b.length + 1)} (hpq : p ≤ q) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightVertex a b p ≤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightVertex a b q := Nat.add_le_add_left hpq _

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (rightVertex_mono)


/-- 左の同方向区間の全列は、連結語でも同じ方向。 -/
lemma append_left_direction (a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction) (p q : Fin (a.length + 1))
    (hd : ∀ j : Fin a.length, p.val ≤ j.val → j.val < q.val → a.direction j = d)
    (i : Fin (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a b).length) (hi : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftVertex a b p).val ≤ i.val)
    (hi' : i.val < (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftVertex a b q).val) : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a b).direction i = d := by
  have hq := q.isLt
  let j : Fin a.length := ⟨i.val, by change i.val < q.val at hi'; omega⟩
  have hij : i = j.castAdd b.length := Fin.ext rfl
  exact (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a b).direction hij).trans
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append_direction_left a b j).trans (hd j hi hi'))

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (append_left_direction)


/-- 右の同方向区間の全列も、接合点を含めて連結語で同じ方向。 -/
lemma append_right_direction (a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction) (p q : Fin (b.length + 1))
    (hd : ∀ j : Fin b.length, p.val ≤ j.val → j.val < q.val → b.direction j = d)
    (i : Fin (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a b).length) (hi : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightVertex a b p).val ≤ i.val)
    (hi' : i.val < (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightVertex a b q).val) : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a b).direction i = d := by
  have hb : i.val < a.length + b.length := i.isLt
  change a.length + p.val ≤ i.val at hi
  change i.val < a.length + q.val at hi'
  let j : Fin b.length := ⟨i.val - a.length, by omega⟩
  have hij : i = j.natAdd a.length := Fin.ext (by dsimp [j]; omega)
  exact (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a b).direction hij).trans
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append_direction_right a b j).trans (hd j (by dsimp [j]; omega) (by dsimp [j]; omega)))

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (append_right_direction)


lemma rightVertex_sub (a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (p q : Fin (b.length + 1)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightVertex a b q).val - (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightVertex a b p).val = q.val - p.val := by
  dsimp [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightVertex]
  omega

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (rightVertex_sub)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
