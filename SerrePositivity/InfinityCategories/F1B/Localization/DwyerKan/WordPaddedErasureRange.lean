module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.WordPaddedBackwardBounds
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.WordErasure

/-!
# padding された元の一列挿入の像

概要：元の eraseInclusion を padding した写像が欠く列は、元の内部の指定列だけ。
方針：連結写像の左右の像を回収して元の eraseInclusion の像へ戻す。
規約：padding の二境界列は像に含める。元の列番号を保持する。
使われ方：padding 後の削除語と全体の削除語の厳密な比較同型。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.Word
open CategoryTheory

abbrev paddedEraseMap (w : Word) (p : Fin w.length) :=
  paddingFunctor.map (eraseInclusion w p)

lemma paddedEraseMap_injective (w : Word) (p : Fin w.length) :
    Function.Injective (paddedEraseMap w p).orderHom :=
  sandwichMap_injective _ _ _ (eraseInclusion_injective w p)

lemma paddedEraseMap_range (w : Word) (p : Fin w.length) :
    Set.range (paddedEraseMap w p).orderHom = {paddedColumn w p}ᶜ := by
  ext j
  change j ∈ Set.range (appendMap (𝟙 (single .backward))
    (appendMap (eraseInclusion w p) (𝟙 (single .backward)))).orderHom ↔ j ≠ paddedColumn w p
  cases j using Fin.addCases with
  | left j =>
    rw [appendMap_range_left]
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
    rw [appendMap_range_right]
    cases j using Fin.addCases with
    | left j =>
      rw [appendMap_range_left, eraseInclusion_range]
      change (j ≠ p) ↔ (j.castAdd 1).natAdd 1 ≠ paddedColumn w p
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
      rw [appendMap_range_right]
      constructor
      · intro _ hj
        have he := congrArg Fin.val hj
        have hi := p.isLt
        change 1 + (w.length + j.val) = 1 + p.val at he
        omega
      · intro _
        exact ⟨j, rfl⟩

end SerrePositivity.EInfinity.Hammock.Word
