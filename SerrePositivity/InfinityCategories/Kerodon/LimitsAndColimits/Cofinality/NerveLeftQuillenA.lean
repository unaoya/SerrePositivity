module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.QuillenALeft
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.LeftKanShapeIso
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.WeakHomotopyInverse

/-!
概要：通常の左commaのnerveの弱可縮性から、元のnerve写像のleft cofinal性を得る。
方針：射影を保つ既存の左Kan添字の同型で、left Quillen Aのslice条件へ移す。
規約：commaの始対象やnerveのKan性を追加仮定にしない。
使われ方：G9-1、BSの弱終対象のČech形状による極限計算。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality

/-- 通常の各左commaのnerveが弱可縮なら、元の関手のnerveはleft cofinal。 -/
lemma nerveMap_isLeftCofinal_of_weaklyContractible_comma
    {P Q : Type u} [Category.{u} P] [Category.{u} Q] (F : P ⥤ Q)
    (h : ∀ q : Q, IsWeaklyContractible (nerve (CostructuredArrow F q))) :
    IsLeftCofinal (nerveMap F) := by
  apply isLeftCofinal_of_weaklyContractible_slices
  intro v
  obtain ⟨q, rfl⟩ := nerveEquiv.symm.surjective v
  exact (qCatEquivalenceOfIso (nerveLeftKanShapeIso F q)).isQCatEquivalence.isWeakHomotopyEquivalence
    |>.weaklyContractible_iff.mp (h q)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality
