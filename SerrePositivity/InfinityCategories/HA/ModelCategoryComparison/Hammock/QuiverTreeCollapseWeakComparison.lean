module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.QuiverTreeDeformation
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.RelativeNaturalWeakComparison
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.RelativeFunctorLaws

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
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.QuiverTree
open _root_.CategoryTheory _root_.SerrePositivity.InfinityCategories
attribute [local instance] Classical.propDecidable

variable {Q : Type u} [Quiver.{v} Q] {T : WideSubquiver (Quiver.Symmetrify Q)}
  [Quiver.Arborescence T] {S : Finset Q} (D : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeafDeletion T S)

def _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.QuiverTree.LeafDeletion.collapseRelative :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S
    LocalizerMorphism (⊤ : MorphismProperty (Paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S)))
      (⊤ : MorphismProperty (Paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S))) := by
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S
  exact ⟨D.collapseFunctor, fun _ _ _ _ => trivial⟩

lemma _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.QuiverTree.LeafDeletion.collapse_colimitMap_isWeakHomotopyEquivalence :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S
    ∀ x y : Paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S),
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Relative.colimitMap (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.QuiverTree.LeafDeletion.collapseRelative D) x y) := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S
  intro x y
  have hid : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Relative.colimitMap
      (LocalizerMorphism.id (⊤ : MorphismProperty (Paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S)))) x y) := by
    rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Relative.colimitMap_id]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.isWeakHomotopyEquivalence_id _
  cases D.deformation with
  | inl η =>
    exact (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.RelativeNatural.weak_iff (F := (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.QuiverTree.LeafDeletion.collapseRelative D))
      (G := LocalizerMorphism.id _) η (fun _ => trivial) x y).mpr hid
  | inr η =>
    exact (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.RelativeNatural.weak_iff (F := LocalizerMorphism.id _)
      (G := (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.QuiverTree.LeafDeletion.collapseRelative D)) η (fun _ => trivial) x y).mp hid

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.QuiverTree
