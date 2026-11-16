module

public import SerrePositivity.EInfinity.Hammock.TwoSidedWeightedLeftSourceCalculation
public import SerrePositivity.EInfinity.Hammock.TwoSidedMixedLabelNaturality
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ThomasonInversion

/-!
# 元の重み付き左比較自身の弱同値性

概要：固定した任意の右集合ラベルに対し、元の左比較射自身は弱ホモトピー同値。
方針：元の始域同型で既存の一方向 Thomason 比較の反転を移し、同じ全射列へ回収する。
規約：比較射の弱同値性は入力にせず、元の反転・圏同値・一方向定理から証明する。
使われ方：DK9.5の二方向比較の元の各行の弱同値性。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.TwoSidedWeightedLeft
open CategoryTheory Opposite SerrePositivity.InfinityCategories
open SerrePositivity.KST.ProExcision

variable {W : Type u} [Category.{u} W] (F : Wᵒᵖ ⥤ Cat.{u, u}) (S : W ⥤ Type u)

lemma map_eq_transport :
    map F S = (TwoSidedWeightedLeftSource.spaceIso F S).hom ≫
      SSet.opFunctor.map (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.Thomason.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedMixedLabel.pulledDiagram F S)) ≫
        (nerveOppositeIso (Grothendieck (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedMixedLabel.pulledDiagram F S))).inv ≫
          nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedMixedLabel.toMixed F S) := by
  ext n e
  change (map F S).app n e =
    (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedMixedLabel.toMixed F S)).app n
      ((nerveOppositeIso (Grothendieck
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedMixedLabel.pulledDiagram F S))).inv.app n
        ((SSet.opFunctor.map (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.Thomason.map
          (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedMixedLabel.pulledDiagram F S))).app n
          ((TwoSidedWeightedLeftSource.spaceIso F S).hom.app n e)))
  rw [TwoSidedWeightedLeftSource.spaceIso_hom_app F S n.unop.len e]
  change simplex F S e =
    nerveOppositeSimplex (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.Thomason.simplex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedMixedLabel.pulledDiagram F S)
      (TwoSidedWeightedLeftSource.barSimplex F S e)) ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedMixedLabel.toMixed F S
  rw [TwoSidedWeightedLeftSource.simplex_transport, nerveOppositeSimplex_oppositeNerveSimplex]
  rfl

lemma map_isWeakHomotopyEquivalence : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (map F S) := by
  rw [map_eq_transport F S]
  have hA := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso
    (TwoSidedWeightedLeftSource.spaceIso F S)).isWeakHomotopyEquivalence
  have hB := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.opposite_map_isWeakHomotopyEquivalence _
    (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.Thomason.map_isWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedMixedLabel.pulledDiagram F S))
  have hC := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso
    (nerveOppositeIso (Grothendieck
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedMixedLabel.pulledDiagram F S))).symm).isWeakHomotopyEquivalence
  have hD := TwoSidedMixedLabel.toMixed_nerveMap_isWeakHomotopyEquivalence F S
  exact hA.comp (hB.comp (hC.comp hD))

end SerrePositivity.EInfinity.Hammock.TwoSidedWeightedLeft
