module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.QuiverTreeCollapseWeakComparison
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.WeakTwoOfSix

/-!
# 葉の除去による実際の hammock の可縮性の帰納段階

概要：残りの自由圏の全 hammock が可縮なら元の自由圏でも可縮となる。
方針：元の R・J と同じ colimitMap の因数分解に二対六則を適用する。
規約：元の任意の端点と葉を含む全行を保持する。
使われ方：根に閉じた有限部分木の頂点数による帰納。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.QuiverTree
open _root_.CategoryTheory _root_.SerrePositivity.InfinityCategories
attribute [local instance] Classical.propDecidable

variable {Q : Type u} [Quiver.{v} Q] {T : WideSubquiver (Quiver.Symmetrify Q)}
  [Quiver.Arborescence T] {S : Finset Q} (D : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeafDeletion T S)

lemma _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.QuiverTree.LeafDeletion.collapseRelative_eq_comp :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver (S.erase D.leaf)
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.QuiverTree.LeafDeletion.collapseRelative D) = D.retractionRelative.comp D.inclusionRelative := rfl

lemma _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.QuiverTree.LeafDeletion.collapse_colimitMap_factor :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver (S.erase D.leaf)
    ∀ x y : Paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S), _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Relative.colimitMap (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.QuiverTree.LeafDeletion.collapseRelative D) x y =
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Relative.colimitMap D.retractionRelative x y ≫
        _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Relative.colimitMap D.inclusionRelative
          (D.retractionRelative.functor.obj x) (D.retractionRelative.functor.obj y) := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver (S.erase D.leaf)
  intro x y
  exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Relative.colimitMap_comp D.retractionRelative D.inclusionRelative x y

lemma _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.QuiverTree.LeafDeletion.contractible_of_remaining
    (hrem : letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver (S.erase D.leaf)
      ∀ x y : Paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex (S.erase D.leaf)),
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph
          (⊤ : MorphismProperty (Paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex (S.erase D.leaf)))) x y)) :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S
    ∀ x y : Paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S),
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph
        (⊤ : MorphismProperty (Paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S))) x y) := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver (S.erase D.leaf)
  intro x y
  apply _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.contractible_of_weak_factor (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Relative.colimitMap D.retractionRelative x y)
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Relative.colimitMap D.inclusionRelative
      (D.retractionRelative.functor.obj x) (D.retractionRelative.functor.obj y))
  · rw [← (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.QuiverTree.LeafDeletion.collapse_colimitMap_factor D)]
    exact (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.QuiverTree.LeafDeletion.collapse_colimitMap_isWeakHomotopyEquivalence D) x y
  · exact hrem _ _

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.QuiverTree
