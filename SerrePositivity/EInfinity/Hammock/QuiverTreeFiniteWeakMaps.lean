module

public import SerrePositivity.EInfinity.Hammock.QuiverTreeFiniteContractible
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiverRelative
public import SerrePositivity.EInfinity.Hammock.ContractibleMaps

/-!
# 元の有限部分木の包含と葉の除去の弱比較

概要：包含と葉の除去自体も元の全端点で弱ホモトピー同値を与える。
方針：証明済みの両側の可縮性と元の比較射を使う。
規約：元の subsetRelative・retractionRelative・inclusionRelative を保つ。
使われ方：全被覆への有限部分木の余極限。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.QuiverTree
open CategoryTheory SerrePositivity.InfinityCategories
attribute [local instance] Classical.propDecidable

variable {Q : Type u} [Quiver.{v} Q] (T : WideSubquiver (Quiver.Symmetrify Q))
  [Quiver.Arborescence T] [Quiver.IsThin (Quiver.FreeGroupoid Q)]
  {S R : Finset Q}

lemma subset_colimitMap_isWeakHomotopyEquivalence (hS : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootClosed T S) (hR : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootClosed T R)
    (h : S ⊆ R) :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver R
    ∀ x y : Paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S),
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (Relative.colimitMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.subsetRelative h) x y) := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver R
  intro x y
  exact weak_of_contractible _ (finite_colimit_isWeaklyContractible T S hS x y)
    (finite_colimit_isWeaklyContractible T R hR _ _)

lemma LeafDeletion.retraction_colimitMap_isWeakHomotopyEquivalence
    (D : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeafDeletion T S) (hS : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootClosed T S) :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver (S.erase D.leaf)
    ∀ x y : Paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S),
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (Relative.colimitMap D.retractionRelative x y) := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver (S.erase D.leaf)
  intro x y
  exact weak_of_contractible _ (finite_colimit_isWeaklyContractible T S hS x y)
    (finite_colimit_isWeaklyContractible T (S.erase D.leaf) D.remaining_closed _ _)

lemma LeafDeletion.inclusion_colimitMap_isWeakHomotopyEquivalence
    (D : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeafDeletion T S) (hS : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootClosed T S) :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver (S.erase D.leaf)
    ∀ x y : Paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex (S.erase D.leaf)),
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (Relative.colimitMap D.inclusionRelative x y) := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver (S.erase D.leaf)
  intro x y
  exact weak_of_contractible _
    (finite_colimit_isWeaklyContractible T (S.erase D.leaf) D.remaining_closed x y)
    (finite_colimit_isWeaklyContractible T S hS _ _)

end SerrePositivity.EInfinity.Hammock.QuiverTree
