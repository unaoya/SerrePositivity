module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.QuiverTreeRetractionRelative

/-!
# 葉の除去と元の包含の逆順の合成

概要：元の有限自由圏上の合成関手の対象を元の頂点へ照合する。
方針：葉では元の親、それ以外では元の頂点を回収する。
規約：元の関手と元の頂点部分型を保持する。
使われ方：逆順の合成から恒等関手への変形。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.QuiverTree
open CategoryTheory

attribute [local instance] Classical.propDecidable

variable {Q : Type u} [Quiver.{v} Q] {T : WideSubquiver (Quiver.Symmetrify Q)}
  [Quiver.Arborescence T] {S : Finset Q} (D : LeafDeletion T S)

def LeafDeletion.parentVertex : FiniteQuiver.Vertex S := ⟨D.parent, D.parent_mem_original⟩

def LeafDeletion.leafVertex : FiniteQuiver.Vertex S := ⟨D.leaf, D.leaf_mem⟩

def LeafDeletion.collapsedVertex (x : FiniteQuiver.Vertex S) : FiniteQuiver.Vertex S :=
  ⟨(D.retractVertex x).val, (Finset.mem_erase.mp (D.retractVertex x).property).2⟩

def LeafDeletion.collapseFunctor :
    letI := FiniteQuiver.quiver S
    Paths (FiniteQuiver.Vertex S) ⥤ Paths (FiniteQuiver.Vertex S) := by
  letI := FiniteQuiver.quiver S
  letI := FiniteQuiver.quiver (S.erase D.leaf)
  exact D.retractionFunctor ⋙ D.inclusionFunctor

lemma LeafDeletion.collapsedVertex_of_ne (x : FiniteQuiver.Vertex S) (hx : x.val ≠ D.leaf) :
    D.collapsedVertex x = x :=
  Subtype.ext (congrArg (fun z : FiniteQuiver.Vertex (S.erase D.leaf) => z.val)
    (D.retractVertex_of_ne x hx))

lemma LeafDeletion.collapsedVertex_leaf (x : FiniteQuiver.Vertex S) (hx : x.val = D.leaf) :
    D.collapsedVertex x = D.parentVertex :=
  Subtype.ext (congrArg (fun z : FiniteQuiver.Vertex (S.erase D.leaf) => z.val)
    (D.retractVertex_leaf x hx))

lemma LeafDeletion.collapseFunctor_obj :
    letI := FiniteQuiver.quiver S
    ∀ x : FiniteQuiver.Vertex S,
      D.collapseFunctor.obj ((Paths.of (FiniteQuiver.Vertex S)).obj x) =
        (Paths.of (FiniteQuiver.Vertex S)).obj (D.collapsedVertex x) := by
  let := FiniteQuiver.quiver S
  intro x
  rfl

lemma LeafDeletion.collapse_obj_of_ne (x : FiniteQuiver.Vertex S) (hx : x.val ≠ D.leaf) :
    letI := FiniteQuiver.quiver S
    D.collapseFunctor.obj ((Paths.of (FiniteQuiver.Vertex S)).obj x) =
      (Paths.of (FiniteQuiver.Vertex S)).obj x := by
  let := FiniteQuiver.quiver S
  exact (D.collapseFunctor_obj x).trans
    (congrArg (Paths.of (FiniteQuiver.Vertex S)).obj (D.collapsedVertex_of_ne x hx))

lemma LeafDeletion.collapse_obj_leaf (x : FiniteQuiver.Vertex S) (hx : x.val = D.leaf) :
    letI := FiniteQuiver.quiver S
    D.collapseFunctor.obj ((Paths.of (FiniteQuiver.Vertex S)).obj x) =
      (Paths.of (FiniteQuiver.Vertex S)).obj D.parentVertex := by
  let := FiniteQuiver.quiver S
  exact (D.collapseFunctor_obj x).trans
    (congrArg (Paths.of (FiniteQuiver.Vertex S)).obj (D.collapsedVertex_leaf x hx))

end SerrePositivity.EInfinity.Hammock.QuiverTree
