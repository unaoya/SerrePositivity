module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.RootedFiniteHammockColimit
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.WeakFiniteSubsetColimit
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.QuiverTreeFiniteContractible

/-!
# 根付き木の全体の元の hammock の弱可縮性

概要：有限包の実際の hammock の可縮性を全体へ移す。
方針：有限部分集合の filtered 余極限と全語の余極限の交換を使う。
規約：元の全端点と全語の hammock を保持する。
使われ方：自由被覆の評価の fiber の可縮性。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.RootedFinite
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.SerrePositivity.InfinityCategories
attribute [local instance] Classical.propDecidable

variable {Q : Type u} [Quiver.{v} Q] (T : WideSubquiver (Quiver.Symmetrify Q))
  [Quiver.Arborescence T] [Quiver.IsThin (Quiver.FreeGroupoid Q)] (X Y : Q)

lemma hammockDiagram_obj_isWeaklyContractible (S : Finset Q) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.RootedFinite.hammockDiagram T X Y).obj S) := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootedFiniteCategory.hull T X Y S)
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible (colimit ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootedFiniteBidiagram.graphWordDiagram T X Y).flip.obj S))
  rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.RootedFinite.wordDiagram_eq]
  exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.QuiverTree.finite_colimit_isWeaklyContractible T (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootedFiniteCategory.hull T X Y S)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.endpointHull_closed T X Y S) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootedFiniteCategory.left T X Y S) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootedFiniteCategory.right T X Y S)

include T in
lemma colimit_isWeaklyContractible :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph (⊤ : MorphismProperty (Paths Q))
      ((Paths.of Q).obj X) ((Paths.of Q).obj Y)) := by
  have h := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.finiteSubsetColimit_isWeaklyContractible (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.RootedFinite.hammockDiagram T X Y)
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.RootedFinite.hammockDiagram_obj_isWeaklyContractible T X Y)
  let e := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.RootedFinite.hammockColimitIso T X Y
  have he := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso e).isWeakHomotopyEquivalence
  have ht : e.hom ≫ terminal.from _ = terminal.from _ := terminal.hom_ext _ _
  apply he.cancel_left
  rw [ht]
  exact h

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.RootedFinite
