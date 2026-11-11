module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.TerminalApexColimit
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.FilteredUniverse
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.Definition
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.CoconeTransformationPointPost
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpaceTerminalValues
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeInitialBoundaryCriterion

/-!
概要：元の始対象は、任意の小さい無限 κ の κ-filtered 余極限に関して compact。
方針：元の全 Hom の各値の可縮性と、一般 coherent filtered 図式の終対象値の交換を使う。
規約：添字と標的の宇宙を分け、元の指定余錐像の全体の余極限性を証明する。
使われ方：compact 対象の有限余極限閉性の空形状。

対応節は Kerodon 9.2（Tag 0639）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects

/-- 元の始対象からの全共変 Hom の各値は、同じ空間の頂点として終対象。 -/
lemma covariantRepresentableValue_isTerminal_of_initial {C : SSet.{u}} [Quasicategory C]
    {x : C _⦋0⦌} (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex x) (y : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.covariantRepresentableInfinity x).app (Opposite.op ⦋0⦌) (ULift.up y)) := by
  apply (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.spaceInfinity_isTerminal_iff_value_isContractibleKan _).mpr
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.covariantRepresentableValueEquivalence x y).isContractibleKan_iff.mpr
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanInitialVertex_pinchedHom_isContractibleKan hx y)

/-- 元の始対象は、添字より大きい標的でも無限 κ に関して κ-compact。 -/
lemma isKappaCompact_of_isInitialVertex {κ : Cardinal.{u}} (hκ : Cardinal.aleph0 ≤ κ)
    {C : SSet.{max u v}} [Quasicategory C] {x : C _⦋0⦌} (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex x) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, v} κ x := by
  intro I hI hFiltered D c _hc
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsFilteredInfinity I := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isFilteredInfinity_of_isKappaFiltered hκ I
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsFilteredInfinity ((SSet.uliftFunctor.{v, u}).obj I) := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.isFilteredInfinity_ulift I
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.isColimitCone_of_terminal_values
    ((SSet.uliftFunctor.{max u v + 1, max u v}).map D ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.covariantRepresentableInfinity x)
  · intro i
    exact covariantRepresentableValue_isTerminal_of_initial hx (D.app (Opposite.op ⦋0⦌) i)
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.mapJoinCocone_vertex, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCocone.ulift_vertex]
    exact covariantRepresentableValue_isTerminal_of_initial hx c.vertex

/-- 空形状の余極限頂点は、同じ宇宙の compact 対象。 -/
lemma isCompact_of_isInitialVertex {C : SSet.{u}} [Quasicategory C]
    {x : C _⦋0⦌} (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex x) : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsCompact x :=
  isKappaCompact_of_isInitialVertex le_rfl hx

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects
