module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.QuiverTreeDeformationComponents

/-!
# 葉の変形の生成辺での自然性

概要：接続辺の向きに応じた成分が全生成辺に自然であることを示す。
方針：葉以外では両端の等式を消去し、葉では元の接続辺の一意性を使う。
規約：元の有限頂点の自由圏上で検証する。
使われ方：全射列への自然変換の延長。

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

lemma LeafDeletion.positiveComponent_generator (g : D.parent ⟶ D.leaf)
    (hg : D.edge.val = g.toPos) :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S
    ∀ {x y : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S} (f : x ⟶ y),
      D.collapseFunctor.map ((Paths.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S)).map f) ≫
        D.positiveComponent g y =
      D.positiveComponent g x ≫ (Paths.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S)).map f := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S
  intro x y f
  rcases x with ⟨x, hxS⟩
  rcases y with ⟨y, hyS⟩
  change x ⟶ y at f
  by_cases hx : x = D.leaf
  · subst x
    exact (D.no_outgoing_positive g hg hyS f).elim
  · by_cases hy : y = D.leaf
    · subst y
      obtain ⟨he, hh⟩ := D.incoming_eq_positive g hg hxS f
      subst x
      have hf := eq_of_heq hh
      subst f
      rw [D.positiveComponent_leaf g _ rfl, D.positiveComponent_of_ne g _ D.parent_ne_leaf,
        D.collapse_generator_incident _ (Or.inr rfl)]
      simp
    · rw [D.positiveComponent_of_ne g ⟨x, hxS⟩ hx, D.positiveComponent_of_ne g ⟨y, hyS⟩ hy,
        D.collapse_generator_of_ne (x := ⟨x, hxS⟩) (y := ⟨y, hyS⟩) f hx hy]
      simp

lemma LeafDeletion.negativeComponent_generator (g : D.leaf ⟶ D.parent)
    (hg : D.edge.val = g.toNeg) :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S
    ∀ {x y : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S} (f : x ⟶ y),
      (Paths.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S)).map f ≫ D.negativeComponent g y =
      D.negativeComponent g x ≫
        D.collapseFunctor.map ((Paths.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S)).map f) := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S
  intro x y f
  rcases x with ⟨x, hxS⟩
  rcases y with ⟨y, hyS⟩
  change x ⟶ y at f
  by_cases hy : y = D.leaf
  · subst y
    exact (D.no_incoming_negative g hg hxS f).elim
  · by_cases hx : x = D.leaf
    · subst x
      obtain ⟨he, hh⟩ := D.outgoing_eq_negative g hg hyS f
      subst y
      have hf := eq_of_heq hh
      subst f
      rw [D.negativeComponent_leaf g ⟨D.leaf, hxS⟩ rfl,
        D.negativeComponent_of_ne g ⟨D.parent, hyS⟩ D.parent_ne_leaf,
        D.collapse_generator_incident _ (Or.inl rfl)]
      simp
    · rw [D.negativeComponent_of_ne g ⟨x, hxS⟩ hx, D.negativeComponent_of_ne g ⟨y, hyS⟩ hy,
        D.collapse_generator_of_ne (x := ⟨x, hxS⟩) (y := ⟨y, hyS⟩) f hx hy]
      simp

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
