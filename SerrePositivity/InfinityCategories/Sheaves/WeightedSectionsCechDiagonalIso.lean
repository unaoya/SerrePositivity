module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Sheaves.WeightedSectionsCechDiagonalComponentIso
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FullyFaithfulHomComparison

/-!
概要：元の相対 Čech 対角に沿った切断の比較は全図式で可逆。
方針：関手圏の同型の成分ごとの判定を使う。
  文献対応：HTT 6.2.2.6（集合値重みを持つ Čech 図式の場合）。
使われ方：像への射に沿った切断の可逆性。
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories

namespace SerrePositivity.InfinityCategories.Sheaves

/-- 同じ相対 Čech 対角の比較全体は、指定成分がすべて可逆なので同型。 -/
@[cite HTT "6.2.2.6" (partial := special)
  "小さい通常の site の集合値重みの相対 Čech 図式。"]
lemma weightedSections_relativeCechDiagonalHom_isIso
    {C : Type u} [SmallCategory C] {E : SSet.{u + 1}} [Quasicategory E]
    (J : GrothendieckTopology C) {P Q : Cᵒᵖ ⥤ Type u} (f : P ⟶ Q)
    [CategoryTheory.Presheaf.IsLocallyInjective J f]
    (O : Presheaf C E) (hO : IsSheaf J O)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E) :
    IsIso (weightedSections_relativeCechDiagonalHom f O hE) := by
  apply functorHom_isIso_of_components
  intro j
  have h := weightedSections_relativeCechDiagonalHom_component_isIso J f O hO hE j
  simpa only [functorHomEvaluate, isIso_comp_left_iff, isIso_comp_right_iff] using h

end SerrePositivity.InfinityCategories.Sheaves
