module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.QuiverTreeRetractionRelative

/-!
# 葉の除去と元の包含の逆順の合成

概要：元の有限自由圏上の合成関手の対象を元の頂点へ照合する。
方針：葉では元の親、それ以外では元の頂点を回収する。
規約：元の関手と元の頂点部分型を保持する。
使われ方：逆順の合成から恒等関手への変形。

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

variable {Q : Type u} [Quiver.{v} Q] {T : WideSubquiver (Quiver.Symmetrify Q)}
  [Quiver.Arborescence T] {S : Finset Q} (D : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeafDeletion T S)

def LeafDeletion.parentVertex : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S := ⟨D.parent, D.parent_mem_original⟩

def LeafDeletion.leafVertex : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S := ⟨D.leaf, D.leaf_mem⟩

def LeafDeletion.collapsedVertex (x : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S :=
  ⟨(D.retractVertex x).val, (Finset.mem_erase.mp (D.retractVertex x).property).2⟩

def LeafDeletion.collapseFunctor :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S
    Paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S) ⥤ Paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S) := by
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver (S.erase D.leaf)
  exact D.retractionFunctor ⋙ D.inclusionFunctor

lemma LeafDeletion.collapsedVertex_of_ne (x : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S) (hx : x.val ≠ D.leaf) :
    D.collapsedVertex x = x :=
  Subtype.ext (congrArg (fun z : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex (S.erase D.leaf) => z.val)
    (D.retractVertex_of_ne x hx))

lemma LeafDeletion.collapsedVertex_leaf (x : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S) (hx : x.val = D.leaf) :
    D.collapsedVertex x = D.parentVertex :=
  Subtype.ext (congrArg (fun z : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex (S.erase D.leaf) => z.val)
    (D.retractVertex_leaf x hx))

lemma LeafDeletion.collapseFunctor_obj :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S
    ∀ x : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S,
      D.collapseFunctor.obj ((Paths.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S)).obj x) =
        (Paths.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S)).obj (D.collapsedVertex x) := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S
  intro x
  rfl

lemma LeafDeletion.collapse_obj_of_ne (x : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S) (hx : x.val ≠ D.leaf) :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S
    D.collapseFunctor.obj ((Paths.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S)).obj x) =
      (Paths.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S)).obj x := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S
  exact (D.collapseFunctor_obj x).trans
    (congrArg (Paths.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S)).obj (D.collapsedVertex_of_ne x hx))

lemma LeafDeletion.collapse_obj_leaf (x : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S) (hx : x.val = D.leaf) :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S
    D.collapseFunctor.obj ((Paths.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S)).obj x) =
      (Paths.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S)).obj D.parentVertex := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S
  exact (D.collapseFunctor_obj x).trans
    (congrArg (Paths.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S)).obj (D.collapsedVertex_leaf x hx))

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
