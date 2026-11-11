module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordPaddedBackwardBounds
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordErasure

/-!
# padding された元の一列挿入の像

概要：元の eraseInclusion を padding した写像が欠く列は、元の内部の指定列だけ。
方針：連結写像の左右の像を回収して元の eraseInclusion の像へ戻す。
規約：padding の二境界列は像に含める。元の列番号を保持する。
使われ方：padding 後の削除語と全体の削除語の厳密な比較同型。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

abbrev paddedEraseMap (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (p : Fin w.length) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.eraseInclusion w p)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (paddedEraseMap)


lemma paddedEraseMap_injective (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (p : Fin w.length) :
    Function.Injective (paddedEraseMap w p).orderHom :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.sandwichMap_injective _ _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.eraseInclusion_injective w p)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (paddedEraseMap_injective)


lemma paddedEraseMap_range (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (p : Fin w.length) :
    Set.range (paddedEraseMap w p).orderHom = {_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddedColumn w p}ᶜ := by
  ext j
  change j ∈ Set.range (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.appendMap (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.appendMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.eraseInclusion w p) (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward)))).orderHom ↔ j ≠ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddedColumn w p
  cases j using Fin.addCases with
  | left j =>
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.appendMap_range_left]
    constructor
    · intro _ hj
      have he := congrArg Fin.val hj
      have hi := j.isLt
      change j.val = 1 + p.val at he
      change j.val < 1 at hi
      omega
    · intro _
      exact ⟨j, rfl⟩
  | right j =>
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.appendMap_range_right]
    cases j using Fin.addCases with
    | left j =>
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.appendMap_range_left, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.eraseInclusion_range]
      change (j ≠ p) ↔ (j.castAdd 1).natAdd 1 ≠ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddedColumn w p
      constructor
      · intro hn he
        apply hn
        apply Fin.ext
        have hv := congrArg Fin.val he
        change 1 + j.val = 1 + p.val at hv
        omega
      · intro hn he
        subst j
        exact hn rfl
    | right j =>
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.appendMap_range_right]
      constructor
      · intro _ hj
        have he := congrArg Fin.val hj
        have hi := p.isLt
        change 1 + (w.length + j.val) = 1 + p.val at he
        omega
      · intro _
        exact ⟨j, rfl⟩

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (paddedEraseMap_range)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
