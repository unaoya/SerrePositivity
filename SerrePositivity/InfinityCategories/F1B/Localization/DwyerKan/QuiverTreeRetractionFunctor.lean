module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.QuiverTreeRetractArrow

/-!
# 葉を親へ送る元の自由圏の関手

概要：元の有限部分木の自由圏から葉の除去後の自由圏への関手を構成する。
方針：元の生成辺の像を自由圏の普遍性で延長する。
規約：元の各生成辺の像と除去後の元の包含を公開する。
使われ方：有限部分木の葉の除去による hammock の変形。
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

def LeafDeletion.retractionPrefunctor :
    letI := FiniteQuiver.quiver S
    letI := FiniteQuiver.quiver (S.erase D.leaf)
    FiniteQuiver.Vertex S ⥤q Paths (FiniteQuiver.Vertex (S.erase D.leaf)) := by
  letI := FiniteQuiver.quiver S
  letI := FiniteQuiver.quiver (S.erase D.leaf)
  exact
    { obj := fun x => (Paths.of (FiniteQuiver.Vertex (S.erase D.leaf))).obj (D.retractVertex x)
      map := fun f => D.retractArrow _ _ f }

def LeafDeletion.retractionFunctor :
    letI := FiniteQuiver.quiver S
    letI := FiniteQuiver.quiver (S.erase D.leaf)
    Paths (FiniteQuiver.Vertex S) ⥤ Paths (FiniteQuiver.Vertex (S.erase D.leaf)) := by
  letI := FiniteQuiver.quiver S
  letI := FiniteQuiver.quiver (S.erase D.leaf)
  exact Paths.lift D.retractionPrefunctor

def LeafDeletion.inclusionFunctor :
    letI := FiniteQuiver.quiver S
    letI := FiniteQuiver.quiver (S.erase D.leaf)
    Paths (FiniteQuiver.Vertex (S.erase D.leaf)) ⥤ Paths (FiniteQuiver.Vertex S) := by
  letI := FiniteQuiver.quiver S
  letI := FiniteQuiver.quiver (S.erase D.leaf)
  exact FiniteQuiver.subsetFunctor (Finset.erase_subset D.leaf S)

lemma LeafDeletion.retractionFunctor_generator :
    letI := FiniteQuiver.quiver S
    letI := FiniteQuiver.quiver (S.erase D.leaf)
    ∀ {x y : FiniteQuiver.Vertex S} (f : x ⟶ y),
      D.retractionFunctor.map ((Paths.of (FiniteQuiver.Vertex S)).map f) =
        D.retractArrow x y f := by
  let := FiniteQuiver.quiver S
  let := FiniteQuiver.quiver (S.erase D.leaf)
  intro x y f
  exact Paths.lift_toPath _ f

end SerrePositivity.EInfinity.Hammock.QuiverTree
