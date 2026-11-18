module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.RootedFiniteContractible
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FreeQuiverCoverFiniteContractible
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FreeQuiverCoverHammockFiber

/-!
# 元の自由被覆の hammock と評価の fiber の弱可縮性

概要：元の自由被覆の全端点の hammock と元の評価の各 fiber は弱可縮となる。
方針：被覆の測地木への代入と同じ評価の fiber 同型を使う。
規約：薄さや可縮性を追加入力にしない。
使われ方：指定自由圏の評価と DK の比較。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FreeQuiverCover
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.SerrePositivity.InfinityCategories

variable {Q : Type u} [Quiver.{v} Q] (A : Q)

lemma colimit_isWeaklyContractible :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
    ∀ X Y : Paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A), _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph
      (⊤ : MorphismProperty (Paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A))) X Y) := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.spanningTreeArborescence A
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.groupoid_isThin A
  intro X Y
  exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.RootedFinite.colimit_isWeaklyContractible (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.spanningTree A) X Y

lemma hammockValueFiber_isWeaklyContractible (Y : Paths Q)
    (β : (Quiver.FreeGroupoid.of Q).obj A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.positiveEvaluation.obj Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FreeQuiverCover.hammockValueFiber A Y β) := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  let e := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FreeQuiverCover.hammockValueFiberCoverIso A Y β
  have ht : terminal.from _ = e.hom ≫ terminal.from _ := terminal.hom_ext _ _
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (terminal.from (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FreeQuiverCover.hammockValueFiber A Y β))
  rw [ht]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso e).isWeakHomotopyEquivalence.comp
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FreeQuiverCover.colimit_isWeaklyContractible A _ _)

lemma existingHammockValueFiber_isWeaklyContractible {Q' : Type u} [Quiver.{u} Q']
    (A' : Q') (Y' : Paths Q')
    (β' : (Quiver.FreeGroupoid.of Q').obj A' ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.positiveEvaluation.obj Y') :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SimplicialValueFiber.space
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Zigzag.Value.colimitValue _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.positiveEvaluation _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.positiveEvaluation_inverts_top
        ((Paths.of Q').obj A') Y') β') := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A'
  let e := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FreeQuiverCover.existingHammockValueFiberCoverIso A' Y' β'
  have ht : terminal.from _ = e.hom ≫ terminal.from _ := terminal.hom_ext _ _
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (terminal.from _)
  rw [ht]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso e).isWeakHomotopyEquivalence.comp
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FreeQuiverCover.colimit_isWeaklyContractible A' _ _)

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FreeQuiverCover
