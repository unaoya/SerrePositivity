module

public import SerrePositivity.EInfinity.Hammock.QuiverTreeRootContractible
public import SerrePositivity.EInfinity.Hammock.QuiverTreeLeafContractible

/-!
# 根に閉じた有限部分木の実際の hammock の可縮性

概要：元の有限頂点集合の自由圏の全端点の hammock は弱可縮となる。
方針：最大高さの葉を除き、元の合成の弱同値と二対六則を強い帰納法で使う。
規約：可縮性を追加の入力にせず、元の生成辺と全語の余極限を使う。
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

lemma finite_colimit_isWeaklyContractible (S : Finset Q) (hS : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootClosed T S) :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S
    ∀ x y : Paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S),
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph
        (⊤ : MorphismProperty (Paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S))) x y) := by
  revert hS
  induction S using Finset.strongInductionOn
  rename_i S ih
  intro hS
  by_cases hne : ∃ x ∈ S, (show T from x) ≠ Quiver.root T
  · let D := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.chooseLeafDeletion T hS hne
    have hrem := ih (S.erase D.leaf) (Finset.erase_ssubset D.leaf_mem) D.remaining_closed
    exact (_root_.SerrePositivity.EInfinity.Hammock.QuiverTree.LeafDeletion.contractible_of_remaining D) hrem
  · have hroot : ∀ x ∈ S, (show T from x) = Quiver.root T := by
      intro x hx
      by_contra he
      exact hne ⟨x, hx, he⟩
    exact root_colimit_isWeaklyContractible T hroot

end SerrePositivity.EInfinity.Hammock.QuiverTree
