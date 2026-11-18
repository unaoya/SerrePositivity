module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedBarRows
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.WeakIndexedSum
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.WeakTensor
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.DoubleSimplicialColumnWeak

/-!
# 元の二方向 bar の両係数の弱同値不変性

概要：両係数の成分ごとの弱同値は元の二方向 bar の対角の同じ射を弱同値にする。
方針：元の射列の和表示に直積と任意依存和の弱同値保存を適用し、対角へ戻す。
規約：底の射を全て保持し、値の Kan 性と単体集合モデル構造は要求しない。
使われ方：DK §9.5・10.6の二方向 Grothendieck 比較。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedBar
open _root_.CategoryTheory _root_.Opposite _root_.CategoryTheory.MonoidalCategory _root_.SerrePositivity.InfinityCategories

variable {W : Type u} [Category.{u} W]
  {F F' : Wᵒᵖ ⥤ SSet.{u}} {G G' : W ⥤ SSet.{u}}

lemma flippedRowMap_isWeakHomotopyEquivalence (α : F ⟶ F') (β : G ⟶ G')
    (hα : ∀ w, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (α.app w))
    (hβ : ∀ w, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (β.app w)) (n : SimplexCategoryᵒᵖ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedBar.flippedRowMap α β n) := by
  have hs := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.IndexedSum.map_weak
    (fun c : ComposableArrows W n.unop.len =>
      α.app (op (c.obj (Fin.last n.unop.len))) ⊗ₘ β.app (c.obj 0))
    (fun c => _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.weakTensor (hα _) (hβ _))
  have h :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedBar.rowIso F G n)).isWeakHomotopyEquivalence.comp hs
  rw [← _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedBar.rowIso_naturality α β n] at h
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedBar.rowIso F' G' n)).isWeakHomotopyEquivalence.cancel_right h

lemma map_isWeakHomotopyEquivalence (α : F ⟶ F') (β : G ⟶ G')
    (hα : ∀ w, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (α.app w))
    (hβ : ∀ w, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (β.app w)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedBar.map α β) :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.DoubleSimplicial.diagonalFunctor_map_weak_of_columns (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedBar.rowMap α β)
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedBar.flippedRowMap_isWeakHomotopyEquivalence α β hα hβ)

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedBar
