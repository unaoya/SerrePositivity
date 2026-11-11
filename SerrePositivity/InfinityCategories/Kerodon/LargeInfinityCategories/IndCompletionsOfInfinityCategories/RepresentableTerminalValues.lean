module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.RepresentablePresheafValues
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FunctorTerminal
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpaceTerminalValues
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeInitialBoundaryCriterion

/-!
概要：始対象での表現可能前層の値と、終対象を表す前層の終対象性。
方針：同じ実際の表現可能値と元の写像空間の同値で可縮性を移す。
規約：底は小さい quasicategory。使われ方：Ind の零対象の構成。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

variable {C : SSet.{u}} [Quasicategory C]

/-- 始対象からの全 Hom の可縮性は、表現可能前層の同じ値を空間の終対象にする。 -/
lemma representablePresheafValue_isTerminal_of_initial {z : C _⦋0⦌}
    (hz : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex z) (y : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity y).app (Opposite.op ⦋0⦌)
      (ULift.up (SSet.opObjEquiv.symm z))) := by
  apply (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.spaceInfinity_isTerminal_iff_value_isContractibleKan _).mpr
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafValueEquivalence z y).isContractibleKan_iff.mpr
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanInitialVertex_pinchedHom_isContractibleKan hz y)

/-- 終対象を表す元の前層は、前層 ∞ 圏の終対象。 -/
lemma representablePresheaf_isTerminal_of_terminal {z : C _⦋0⦌}
    (hz : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex z) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity z)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isTerminalVertex_functorVertex_of_pointwise
  rintro ⟨x⟩
  obtain ⟨y, rfl⟩ := SSet.opObjEquiv.symm.surjective x
  apply (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.spaceInfinity_isTerminal_iff_value_isContractibleKan _).mpr
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafValueEquivalence y z).isContractibleKan_iff.mpr
    (hz.pinchedHom_isContractibleKan y)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
