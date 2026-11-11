module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.QuiverTreeRootHeights
public import Mathlib.Data.Finset.Union

/-!
# 根からの元の射列で閉じた有限包

概要：任意の有限頂点集合を含む根に閉じた有限部分木を構成する。
方針：元の根からの射列の有限頂点集合の和を取る。
規約：空集合の包も根を含む。
使われ方：元の全 hammock の有限部分木による表示。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

attribute [local instance] Classical.propDecidable

variable {Q : Type u} [Quiver.{v} Q] (T : WideSubquiver (Quiver.Symmetrify Q))
  [Quiver.Arborescence T]

def RootClosed (S : Finset Q) : Prop :=
  (Quiver.root T : Q) ∈ S ∧ ∀ x ∈ S, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rootVertices T x ⊆ S

def rootHull (S : Finset Q) : Finset Q := insert (Quiver.root T : Q) (S.biUnion (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rootVertices T))

lemma rootHull_empty : rootHull T ∅ = {(Quiver.root T : Q)} := by
  simp [rootHull]

lemma rootHull_root (S : Finset Q) : (Quiver.root T : Q) ∈ rootHull T S :=
  Finset.mem_insert_self _ _

lemma subset_rootHull (S : Finset Q) : S ⊆ rootHull T S := by
  intro x hx
  exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨x, hx, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rootVertices_target T x⟩)

lemma rootHull_closed (S : Finset Q) : RootClosed T (rootHull T S) := by
  refine ⟨rootHull_root T S, ?_⟩
  intro x hx
  rcases Finset.mem_insert.mp hx with hx | hx
  · subst x
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rootVertices_root]
    exact Finset.singleton_subset_iff.mpr (rootHull_root T S)
  · obtain ⟨y, hy, hxy⟩ := Finset.mem_biUnion.mp hx
    intro z hz
    exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr
      ⟨y, hy, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rootVertices_subset_of_mem T hxy hz⟩)

lemma rootHull_minimal {S R : Finset Q} (hR : RootClosed T R) (h : S ⊆ R) :
    rootHull T S ⊆ R := by
  intro x hx
  rcases Finset.mem_insert.mp hx with hx | hx
  · subst x
    exact hR.1
  · obtain ⟨y, hy, hxy⟩ := Finset.mem_biUnion.mp hx
    exact hR.2 y (h hy) hxy

lemma rootHull_of_closed {S : Finset Q} (hS : RootClosed T S) : rootHull T S = S :=
  Finset.Subset.antisymm (rootHull_minimal T hS (Finset.Subset.refl _)) (subset_rootHull T S)

lemma rootHull_idempotent (S : Finset Q) : rootHull T (rootHull T S) = rootHull T S :=
  rootHull_of_closed T (rootHull_closed T S)

lemma rootHull_mono {S R : Finset Q} (h : S ⊆ R) : rootHull T S ⊆ rootHull T R :=
  rootHull_minimal T (rootHull_closed T R) (h.trans (subset_rootHull T R))

lemma RootClosed.union {S R : Finset Q} (hS : RootClosed T S) (hR : RootClosed T R) :
    RootClosed T (S ∪ R) := by
  refine ⟨Finset.mem_union_left _ hS.1, ?_⟩
  intro x hx y hy
  rcases Finset.mem_union.mp hx with hx | hx
  · exact Finset.mem_union_left _ (hS.2 x hx hy)
  · exact Finset.mem_union_right _ (hR.2 x hx hy)

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
