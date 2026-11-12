module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.QuiverTreeLeafEdgeOrientation

/-!
# 元の葉の辺を使う自然変換の成分

概要：葉で元の接続辺、他では元の対象の等式による恒等射を使う。
方針：合成関手の元の対象の回収式に沿って移送する。
規約：接続辺の向きに応じた二つの方向を構成する。
使われ方：葉の除去の元の自然変換。

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

def LeafDeletion.positiveComponent (g : D.parent ⟶ D.leaf) :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S
    ∀ x : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S,
      D.collapseFunctor.obj ((Paths.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S)).obj x) ⟶
        (Paths.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S)).obj x := by
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S
  intro x
  by_cases hx : x.val = D.leaf
  · exact eqToHom (D.collapse_obj_leaf x hx) ≫
      (Paths.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S)).map (show D.parentVertex ⟶ D.leafVertex from g) ≫
        eqToHom (congrArg (Paths.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S)).obj (Subtype.ext hx).symm)
  · exact eqToHom (D.collapse_obj_of_ne x hx)

lemma LeafDeletion.positiveComponent_of_ne (g : D.parent ⟶ D.leaf)
    (x : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S) (hx : x.val ≠ D.leaf) :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S
    D.positiveComponent g x = eqToHom (D.collapse_obj_of_ne x hx) := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S
  exact dite_eq_right hx

lemma LeafDeletion.positiveComponent_leaf (g : D.parent ⟶ D.leaf)
    (x : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S) (hx : x.val = D.leaf) :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S
    D.positiveComponent g x = eqToHom (D.collapse_obj_leaf x hx) ≫
      (Paths.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S)).map (show D.parentVertex ⟶ D.leafVertex from g) ≫
        eqToHom (congrArg (Paths.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S)).obj (Subtype.ext hx).symm) := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S
  exact dite_eq_left hx

def LeafDeletion.negativeComponent (g : D.leaf ⟶ D.parent) :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S
    ∀ x : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S,
      (Paths.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S)).obj x ⟶
        D.collapseFunctor.obj ((Paths.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S)).obj x) := by
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S
  intro x
  by_cases hx : x.val = D.leaf
  · exact eqToHom (congrArg (Paths.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S)).obj (Subtype.ext hx)) ≫
      (Paths.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S)).map (show D.leafVertex ⟶ D.parentVertex from g) ≫
        eqToHom (D.collapse_obj_leaf x hx).symm
  · exact eqToHom (D.collapse_obj_of_ne x hx).symm

lemma LeafDeletion.negativeComponent_of_ne (g : D.leaf ⟶ D.parent)
    (x : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S) (hx : x.val ≠ D.leaf) :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S
    D.negativeComponent g x = eqToHom (D.collapse_obj_of_ne x hx).symm := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S
  exact dite_eq_right hx

lemma LeafDeletion.negativeComponent_leaf (g : D.leaf ⟶ D.parent)
    (x : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S) (hx : x.val = D.leaf) :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S
    D.negativeComponent g x =
      eqToHom (congrArg (Paths.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S)).obj (Subtype.ext hx)) ≫
        (Paths.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S)).map (show D.leafVertex ⟶ D.parentVertex from g) ≫
          eqToHom (D.collapse_obj_leaf x hx).symm := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S
  exact dite_eq_left hx

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
