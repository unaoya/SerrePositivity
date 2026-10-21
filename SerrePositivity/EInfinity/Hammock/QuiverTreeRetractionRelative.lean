module

public import SerrePositivity.EInfinity.Hammock.QuiverTreeRetractionIdentity
public import Mathlib.CategoryTheory.Localization.LocalizerMorphism

/-!
# 全指定自由圏の相対関手としての葉の除去

概要：元の葉の除去と元の包含を全指定自由圏の相対関手へ束ねる。
方針：全ての元の射が指定であることを使う。
規約：底の元の関手と元の厳密な左逆を保持する。
使われ方：葉の除去による元の hammock の比較。
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

def LeafDeletion.retractionRelative :
    letI := FiniteQuiver.quiver S
    letI := FiniteQuiver.quiver (S.erase D.leaf)
    LocalizerMorphism (⊤ : MorphismProperty (Paths (FiniteQuiver.Vertex S)))
      (⊤ : MorphismProperty (Paths (FiniteQuiver.Vertex (S.erase D.leaf)))) := by
  letI := FiniteQuiver.quiver S
  letI := FiniteQuiver.quiver (S.erase D.leaf)
  exact ⟨D.retractionFunctor, fun _ _ _ _ => trivial⟩

def LeafDeletion.inclusionRelative :
    letI := FiniteQuiver.quiver S
    letI := FiniteQuiver.quiver (S.erase D.leaf)
    LocalizerMorphism (⊤ : MorphismProperty (Paths (FiniteQuiver.Vertex (S.erase D.leaf))))
      (⊤ : MorphismProperty (Paths (FiniteQuiver.Vertex S))) := by
  letI := FiniteQuiver.quiver S
  letI := FiniteQuiver.quiver (S.erase D.leaf)
  exact ⟨D.inclusionFunctor, fun _ _ _ _ => trivial⟩

lemma LeafDeletion.inclusion_retraction_underlying :
    letI := FiniteQuiver.quiver S
    letI := FiniteQuiver.quiver (S.erase D.leaf)
    D.inclusionRelative.functor ⋙ D.retractionRelative.functor =
      𝟭 (Paths (FiniteQuiver.Vertex (S.erase D.leaf))) := by
  let := FiniteQuiver.quiver S
  let := FiniteQuiver.quiver (S.erase D.leaf)
  exact D.inclusion_retraction

end SerrePositivity.EInfinity.Hammock.QuiverTree
