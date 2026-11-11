module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallFilteredTotalCofinal
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.Cofinality

/-!
概要：通常の各右 comma に始対象を構成して、同じ nerve 写像の right cofinal 性を得る。
方針：始対象による弱可縮性を F1B の native な comma 同型で移し、Quillen A を適用する。
規約：通常の Final instance や cofinal 性を仮定せず、各始対象のデータを明示引数とする。
使われ方：部分添字 fiber から左 Kan 局所添字への比較。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 通常の各 comma の明示的な始対象は、元の nerve 写像の right cofinal 性を与える。 -/
lemma nerveMap_isRightCofinal_of_initial_comma {P Q : Type u}
    [Category.{u} P] [Category.{u} Q] (F : P ⥤ Q)
    (h : ∀ q : Q, ∃ c : StructuredArrow q F, Nonempty (IsInitial c)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal (nerveMap F) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isRightCofinal_of_weaklyContractible_coslices
  intro v
  obtain ⟨q, rfl⟩ := nerveEquiv.symm.surjective v
  obtain ⟨c, ⟨hc⟩⟩ := h q
  have h0 : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (Δ[0] : SSet.{u}) := by
    intro n b
    exact ⟨stdSimplex.isTerminalObj₀.from _, stdSimplex.isTerminalObj₀.hom_ext _ _⟩
  have hcomma : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible (nerve (StructuredArrow q F)) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.nervePoint_isLeftCofinal hc).isWeakHomotopyEquivalence.weaklyContractible_iff.mp
      h0.isWeaklyContractible
  let e := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveRightKanShapeIso q F ≪≫ pullbackSymmetry _ _
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso e).isQCatEquivalence.isWeakHomotopyEquivalence
    |>.weaklyContractible_iff.mp hcomma

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
