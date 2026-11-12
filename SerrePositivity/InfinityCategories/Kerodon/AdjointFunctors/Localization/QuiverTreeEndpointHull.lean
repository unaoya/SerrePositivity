module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.QuiverTreeFiniteHull

/-!
# 元の二つの端点を含む根に閉じた有限包

概要：任意の有限支持に元の両端を加えて根に閉じた有限部分木で包む。
方針：既存の最小の根に閉じた包を使う。
規約：包含に対して単調で、端点の元の頂点を保持する。
使われ方：全被覆の固定端点の hammock の有限部分木図式。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
attribute [local instance] Classical.propDecidable

variable {Q : Type u} [Quiver.{v} Q] (T : WideSubquiver (Quiver.Symmetrify Q))
  [Quiver.Arborescence T] (X Y : Q)

def endpointHull (S : Finset Q) : Finset Q := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rootHull T (insert X (insert Y S))

lemma endpointHull_left (S : Finset Q) : X ∈ endpointHull T X Y S :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.subset_rootHull T _ (Finset.mem_insert_self _ _)

lemma endpointHull_right (S : Finset Q) : Y ∈ endpointHull T X Y S :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.subset_rootHull T _ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))

lemma subset_endpointHull (S : Finset Q) : S ⊆ endpointHull T X Y S := by
  intro x hx
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.subset_rootHull T _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx))

lemma endpointHull_closed (S : Finset Q) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootClosed T (endpointHull T X Y S) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rootHull_closed T _

lemma endpointHull_mono {S R : Finset Q} (h : S ⊆ R) :
    endpointHull T X Y S ⊆ endpointHull T X Y R :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rootHull_mono T (Finset.insert_subset_insert X (Finset.insert_subset_insert Y h))

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
