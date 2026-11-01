module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.QuiverTreeDeformation
public import SerrePositivity.EInfinity.Hammock.RelativeNaturalWeakComparison
public import SerrePositivity.EInfinity.Hammock.RelativeFunctorLaws

/-!
# 葉を除去して戻す合成による元の hammock の弱同値

概要：有限木の葉の合成関手は全ての元の端点で弱比較を与える。
方針：元の自然変形の向きごとに相対自然変換の弱比較を適用する。
規約：葉が端点である場合も除外せず、同じ元の比較射を保持する。
使われ方：葉の除去の比較と有限部分木の縮約。
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

def LeafDeletion.collapseRelative :
    letI := FiniteQuiver.quiver S
    LocalizerMorphism (⊤ : MorphismProperty (Paths (FiniteQuiver.Vertex S)))
      (⊤ : MorphismProperty (Paths (FiniteQuiver.Vertex S))) := by
  letI := FiniteQuiver.quiver S
  exact ⟨D.collapseFunctor, fun _ _ _ _ => trivial⟩

lemma LeafDeletion.collapse_colimitMap_isWeakHomotopyEquivalence :
    letI := FiniteQuiver.quiver S
    ∀ x y : Paths (FiniteQuiver.Vertex S),
      IsWeakHomotopyEquivalence (Relative.colimitMap D.collapseRelative x y) := by
  let := FiniteQuiver.quiver S
  intro x y
  have hid : IsWeakHomotopyEquivalence (Relative.colimitMap
      (LocalizerMorphism.id (⊤ : MorphismProperty (Paths (FiniteQuiver.Vertex S)))) x y) := by
    rw [Relative.colimitMap_id]
    exact isWeakHomotopyEquivalence_id _
  cases D.deformation with
  | inl η =>
    exact (RelativeNatural.weak_iff (F := D.collapseRelative)
      (G := LocalizerMorphism.id _) η (fun _ => trivial) x y).mpr hid
  | inr η =>
    exact (RelativeNatural.weak_iff (F := LocalizerMorphism.id _)
      (G := D.collapseRelative) η (fun _ => trivial) x y).mp hid

end SerrePositivity.EInfinity.Hammock.QuiverTree
