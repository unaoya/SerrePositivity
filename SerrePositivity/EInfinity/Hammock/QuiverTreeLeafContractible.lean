module

public import SerrePositivity.EInfinity.Hammock.QuiverTreeCollapseWeakComparison
public import SerrePositivity.EInfinity.Hammock.WeakTwoOfSix

/-!
# 葉の除去による実際の hammock の可縮性の帰納段階

概要：残りの自由圏の全 hammock が可縮なら元の自由圏でも可縮となる。
方針：元の R・J と同じ colimitMap の因数分解に二対六則を適用する。
規約：元の任意の端点と葉を含む全行を保持する。
使われ方：根に閉じた有限部分木の頂点数による帰納。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.QuiverTree
open CategoryTheory SerrePositivity.InfinityCategories
attribute [local instance] Classical.propDecidable

variable {Q : Type u} [Quiver.{v} Q] {T : WideSubquiver (Quiver.Symmetrify Q)}
  [Quiver.Arborescence T] {S : Finset Q} (D : LeafDeletion T S)

lemma LeafDeletion.collapseRelative_eq_comp :
    letI := FiniteQuiver.quiver S
    letI := FiniteQuiver.quiver (S.erase D.leaf)
    D.collapseRelative = D.retractionRelative.comp D.inclusionRelative := rfl

lemma LeafDeletion.collapse_colimitMap_factor :
    letI := FiniteQuiver.quiver S
    letI := FiniteQuiver.quiver (S.erase D.leaf)
    ∀ x y : Paths (FiniteQuiver.Vertex S), Relative.colimitMap D.collapseRelative x y =
      Relative.colimitMap D.retractionRelative x y ≫
        Relative.colimitMap D.inclusionRelative
          (D.retractionRelative.functor.obj x) (D.retractionRelative.functor.obj y) := by
  let := FiniteQuiver.quiver S
  let := FiniteQuiver.quiver (S.erase D.leaf)
  intro x y
  exact Relative.colimitMap_comp D.retractionRelative D.inclusionRelative x y

lemma LeafDeletion.contractible_of_remaining
    (hrem : letI := FiniteQuiver.quiver (S.erase D.leaf)
      ∀ x y : Paths (FiniteQuiver.Vertex (S.erase D.leaf)),
        IsWeaklyContractible (colimitGraph
          (⊤ : MorphismProperty (Paths (FiniteQuiver.Vertex (S.erase D.leaf)))) x y)) :
    letI := FiniteQuiver.quiver S
    ∀ x y : Paths (FiniteQuiver.Vertex S),
      IsWeaklyContractible (colimitGraph
        (⊤ : MorphismProperty (Paths (FiniteQuiver.Vertex S))) x y) := by
  let := FiniteQuiver.quiver S
  let := FiniteQuiver.quiver (S.erase D.leaf)
  intro x y
  apply contractible_of_weak_factor (Relative.colimitMap D.retractionRelative x y)
    (Relative.colimitMap D.inclusionRelative
      (D.retractionRelative.functor.obj x) (D.retractionRelative.functor.obj y))
  · rw [← D.collapse_colimitMap_factor]
    exact D.collapse_colimitMap_isWeakHomotopyEquivalence x y
  · exact hrem _ _

end SerrePositivity.EInfinity.Hammock.QuiverTree
