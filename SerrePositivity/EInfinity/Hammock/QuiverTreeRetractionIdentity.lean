module

public import SerrePositivity.EInfinity.Hammock.QuiverTreeRetractionFunctor

/-!
# 葉の除去後の元の自由圏の回収

概要：元の包含の後に葉を親へ送ると、残りの自由圏の恒等関手になる。
方針：残った元の頂点と元の各生成辺を照合する。
規約：自然同型だけでなく元の関手の厳密な等式を証明する。
使われ方：有限部分木の葉の除去による変形。
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

lemma LeafDeletion.retractVertex_inclusion (x : FiniteQuiver.Vertex (S.erase D.leaf)) :
    D.retractVertex (⟨x.val, (Finset.mem_erase.mp x.property).2⟩ : FiniteQuiver.Vertex S) = x := by
  apply Subtype.ext
  simp [LeafDeletion.retractVertex, (Finset.mem_erase.mp x.property).1]

lemma LeafDeletion.retractArrow_of_ne (x y : FiniteQuiver.Vertex S) (f : x.val ⟶ y.val)
    (hx : x.val ≠ D.leaf) (hy : y.val ≠ D.leaf) :
    letI := FiniteQuiver.quiver (S.erase D.leaf)
    let x' : FiniteQuiver.Vertex (S.erase D.leaf) :=
      ⟨x.val, Finset.mem_erase.mpr ⟨hx, x.property⟩⟩
    let y' : FiniteQuiver.Vertex (S.erase D.leaf) :=
      ⟨y.val, Finset.mem_erase.mpr ⟨hy, y.property⟩⟩
    let g : x' ⟶ y' := f
    D.retractArrow x y f =
      eqToHom (congrArg (Paths.of (FiniteQuiver.Vertex (S.erase D.leaf))).obj
        (D.retractVertex_of_ne x hx)) ≫
      (Paths.of (FiniteQuiver.Vertex (S.erase D.leaf))).map g ≫
      eqToHom (congrArg (Paths.of (FiniteQuiver.Vertex (S.erase D.leaf))).obj
        (D.retractVertex_of_ne y hy).symm) := by
  let := FiniteQuiver.quiver (S.erase D.leaf)
  exact dite_eq_right (not_or.mpr ⟨hx, hy⟩)

lemma LeafDeletion.inclusion_retraction :
    letI := FiniteQuiver.quiver S
    letI := FiniteQuiver.quiver (S.erase D.leaf)
    D.inclusionFunctor ⋙ D.retractionFunctor =
      𝟭 (Paths (FiniteQuiver.Vertex (S.erase D.leaf))) := by
  let := FiniteQuiver.quiver S
  let := FiniteQuiver.quiver (S.erase D.leaf)
  have ho : (D.inclusionFunctor ⋙ D.retractionFunctor).obj =
      (𝟭 (Paths (FiniteQuiver.Vertex (S.erase D.leaf)))).obj := by
    funext x
    exact congrArg (Paths.of (FiniteQuiver.Vertex (S.erase D.leaf))).obj
      (D.retractVertex_inclusion x)
  apply Paths.ext_functor ho
  intro x y f
  have hx := (Finset.mem_erase.mp x.property).1
  have hy := (Finset.mem_erase.mp y.property).1
  exact (D.retractionFunctor_generator
    (x := (⟨x.val, (Finset.mem_erase.mp x.property).2⟩ : FiniteQuiver.Vertex S))
    (y := (⟨y.val, (Finset.mem_erase.mp y.property).2⟩ : FiniteQuiver.Vertex S)) f).trans
      (D.retractArrow_of_ne
        (⟨x.val, (Finset.mem_erase.mp x.property).2⟩ : FiniteQuiver.Vertex S)
        (⟨y.val, (Finset.mem_erase.mp y.property).2⟩ : FiniteQuiver.Vertex S) f hx hy)

end SerrePositivity.EInfinity.Hammock.QuiverTree
