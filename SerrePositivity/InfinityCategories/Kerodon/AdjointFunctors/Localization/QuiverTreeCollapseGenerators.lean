module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.QuiverTreeLeafEndofunctor

/-!
# 逆順の合成による元の生成辺の像

概要：葉に接する辺の恒等性と他の辺の元の像を回収する。
方針：元の葉の除去関手の生成辺の式を元の包含で送る。
規約：元の生成辺と端点の等式だけを使う。
使われ方：葉の除去の自然変換の生成辺での自然性。

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

lemma LeafDeletion.collapse_generator :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver (S.erase D.leaf)
    ∀ {x y : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S} (f : x ⟶ y),
      D.collapseFunctor.map ((Paths.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S)).map f) =
        D.inclusionFunctor.map (D.retractArrow x y f) := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver (S.erase D.leaf)
  intro x y f
  exact congrArg D.inclusionFunctor.map (D.retractionFunctor_generator f)

lemma LeafDeletion.collapse_generator_of_ne :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S
    ∀ {x y : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S} (f : x ⟶ y) (hx : x.val ≠ D.leaf) (hy : y.val ≠ D.leaf),
      D.collapseFunctor.map ((Paths.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S)).map f) =
        eqToHom (D.collapse_obj_of_ne x hx) ≫ (Paths.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S)).map f ≫
          eqToHom (D.collapse_obj_of_ne y hy).symm := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver (S.erase D.leaf)
  intro x y f hx hy
  calc
    _ = D.inclusionFunctor.map (D.retractArrow x y f) := D.collapse_generator f
    _ = _ := (congrArg D.inclusionFunctor.map (D.retractArrow_of_ne x y f hx hy)).trans (by
      rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
        eqToHom_map, eqToHom_map]
      rfl)

lemma LeafDeletion.collapsedVertex_incident (x y : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S) (f : x.val ⟶ y.val)
    (h : x.val = D.leaf ∨ y.val = D.leaf) : D.collapsedVertex x = D.collapsedVertex y :=
  Subtype.ext (congrArg (fun z : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex (S.erase D.leaf) => z.val)
    (D.incident_retract_eq x y f h))

lemma LeafDeletion.collapse_generator_incident :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S
    ∀ {x y : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S} (f : x ⟶ y) (h : x.val = D.leaf ∨ y.val = D.leaf),
      D.collapseFunctor.map ((Paths.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S)).map f) =
        eqToHom (congrArg (Paths.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S)).obj
          (D.collapsedVertex_incident x y f h)) := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver (S.erase D.leaf)
  intro x y f h
  exact (D.collapse_generator f).trans
    ((congrArg D.inclusionFunctor.map (D.retractArrow_incident x y f h)).trans
      (eqToHom_map D.inclusionFunctor _))

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
