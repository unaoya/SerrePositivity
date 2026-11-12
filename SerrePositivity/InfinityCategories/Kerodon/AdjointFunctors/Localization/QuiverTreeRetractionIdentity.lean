module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.QuiverTreeRetractionFunctor

/-!
# 葉の除去後の元の自由圏の回収

概要：元の包含の後に葉を親へ送ると、残りの自由圏の恒等関手になる。
方針：残った元の頂点と元の各生成辺を照合する。
規約：自然同型だけでなく元の関手の厳密な等式を証明する。
使われ方：有限部分木の葉の除去による変形。

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

lemma LeafDeletion.retractVertex_inclusion (x : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex (S.erase D.leaf)) :
    D.retractVertex (⟨x.val, (Finset.mem_erase.mp x.property).2⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S) = x := by
  apply Subtype.ext
  simp [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeafDeletion.retractVertex, (Finset.mem_erase.mp x.property).1]

lemma LeafDeletion.retractArrow_of_ne (x y : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S) (f : x.val ⟶ y.val)
    (hx : x.val ≠ D.leaf) (hy : y.val ≠ D.leaf) :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver (S.erase D.leaf)
    let x' : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex (S.erase D.leaf) :=
      ⟨x.val, Finset.mem_erase.mpr ⟨hx, x.property⟩⟩
    let y' : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex (S.erase D.leaf) :=
      ⟨y.val, Finset.mem_erase.mpr ⟨hy, y.property⟩⟩
    let g : x' ⟶ y' := f
    D.retractArrow x y f =
      eqToHom (congrArg (Paths.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex (S.erase D.leaf))).obj
        (D.retractVertex_of_ne x hx)) ≫
      (Paths.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex (S.erase D.leaf))).map g ≫
      eqToHom (congrArg (Paths.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex (S.erase D.leaf))).obj
        (D.retractVertex_of_ne y hy).symm) := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver (S.erase D.leaf)
  exact dite_eq_right (not_or.mpr ⟨hx, hy⟩)

lemma LeafDeletion.inclusion_retraction :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver (S.erase D.leaf)
    D.inclusionFunctor ⋙ D.retractionFunctor =
      𝟭 (Paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex (S.erase D.leaf))) := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver (S.erase D.leaf)
  have ho : (D.inclusionFunctor ⋙ D.retractionFunctor).obj =
      (𝟭 (Paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex (S.erase D.leaf)))).obj := by
    funext x
    exact congrArg (Paths.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex (S.erase D.leaf))).obj
      (D.retractVertex_inclusion x)
  apply Paths.ext_functor ho
  intro x y f
  have hx := (Finset.mem_erase.mp x.property).1
  have hy := (Finset.mem_erase.mp y.property).1
  exact (D.retractionFunctor_generator
    (x := (⟨x.val, (Finset.mem_erase.mp x.property).2⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S))
    (y := (⟨y.val, (Finset.mem_erase.mp y.property).2⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S)) f).trans
      (D.retractArrow_of_ne
        (⟨x.val, (Finset.mem_erase.mp x.property).2⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S)
        (⟨y.val, (Finset.mem_erase.mp y.property).2⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S) f hx hy)

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
