module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Category.Preorder

/-!
# 元の語の長さで制限した全部分圏

概要：長さが n 以下の元の語の全部分圏と、上限を増やす包含を構成する。
方針：元の全色保存単調写像を保持する full subcategory を使う。
規約：次数の上限だけを制限し、全射や単射の射を除かない。
使われ方：Dwyer–Kan §4.2 の長さ濾過。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

def lengthProperty (n : ℕ) : ObjectProperty _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word := fun w => w.length ≤ n

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (lengthProperty)


abbrev LengthBounded (n : ℕ) := (lengthProperty n).FullSubcategory

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (LengthBounded)


def lengthInclusion (n : ℕ) : LengthBounded n ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word := (lengthProperty n).ι

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (lengthInclusion)


def lengthBoundInclusion {n m : ℕ} (h : n ≤ m) : LengthBounded n ⥤ LengthBounded m :=
  ObjectProperty.ιOfLE (fun _ hw => hw.trans h)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (lengthBoundInclusion)


lemma lengthBoundInclusion_comp {n m : ℕ} (h : n ≤ m) :
    lengthBoundInclusion h ⋙ lengthInclusion m = lengthInclusion n := rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (lengthBoundInclusion_comp)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
