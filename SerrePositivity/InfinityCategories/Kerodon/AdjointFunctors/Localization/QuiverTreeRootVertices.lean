module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.PathVertices
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.QuiverTreeHeight

/-!
# 根からの元の一意な射列の有限頂点集合

概要：木の元の根から各頂点へ至る射列の全頂点を回収する。
方針：元の射列の一意性と元の連結の有限集合の式を使う。
規約：部分 quiver の根と元の頂点を保持する。
使われ方：根に閉じた有限部分木の構成。

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

def treePathVertices {x y : T} (p : Quiver.Path x y) : Finset Q :=
  @_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pathVertices T (WideSubquiver.quiver T) x y p

omit [Quiver.Arborescence T] in
lemma treePathVertices_nil (x : T) : treePathVertices T (Quiver.Path.nil : Quiver.Path x x) =
    {(show Q from x)} := @_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pathVertices_nil T (WideSubquiver.quiver T) x

omit [Quiver.Arborescence T] in
lemma treePathVertices_cons {x y z : T} (p : Quiver.Path x y) (e : y ⟶ z) :
    treePathVertices T (p.cons e) = insert (show Q from z) (treePathVertices T p) :=
  @_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pathVertices_cons T (WideSubquiver.quiver T) x y z p e

def rootVertices (x : Q) : Finset Q := treePathVertices T (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rootPath T (show T from x))

lemma rootVertices_eq_of_path {x : T} (p : Quiver.Path (Quiver.root T) x) :
    rootVertices T (show Q from x) = treePathVertices T p :=
  congrArg (treePathVertices T) (Subsingleton.elim (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rootPath T x) p)

lemma rootVertices_root : rootVertices T (Quiver.root T) = {Quiver.root T} :=
  (rootVertices_eq_of_path T Quiver.Path.nil).trans (treePathVertices_nil T _)

lemma rootVertices_target (x : Q) : x ∈ rootVertices T x :=
  @_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pathVertices_target T (WideSubquiver.quiver T) _ _ _

lemma rootVertices_source (x : Q) : (Quiver.root T : Q) ∈ rootVertices T x :=
  @_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pathVertices_source T (WideSubquiver.quiver T) _ _ _

lemma rootVertices_arrow {x y : T} (e : x ⟶ y) :
    rootVertices T (show Q from y) = insert (show Q from y) (rootVertices T (show Q from x)) :=
  (rootVertices_eq_of_path T ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rootPath T x).cons e)).trans (treePathVertices_cons T _ _)

lemma rootVertices_subset_path {x : T} (p : Quiver.Path (Quiver.root T) x) :
    ∀ {y : Q}, y ∈ treePathVertices T p → rootVertices T y ⊆ treePathVertices T p := by
  classical
  induction p with
  | nil =>
    intro y hy
    have he : y = (Quiver.root T : Q) := by simpa [treePathVertices_nil] using hy
    subst y
    exact (rootVertices_eq_of_path T Quiver.Path.nil).le
  | @cons x y p e ih =>
    intro z hz
    rw [treePathVertices_cons] at hz
    rcases Finset.mem_insert.mp hz with hz | hz
    · subst z
      exact (rootVertices_eq_of_path T (p.cons e)).le
    · exact (ih hz).trans (by rw [treePathVertices_cons]; exact Finset.subset_insert _ _)

lemma rootVertices_subset_of_mem {x y : Q} (h : y ∈ rootVertices T x) :
    rootVertices T y ⊆ rootVertices T x := rootVertices_subset_path T _ h

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
