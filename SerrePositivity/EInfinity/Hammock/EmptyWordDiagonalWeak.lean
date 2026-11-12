module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeEmptyZigzagEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordDiagonalAugmentation
public import SerrePositivity.EInfinity.Hammock.DoubleSimplicialWeak
public import SerrePositivity.EInfinity.Hammock.NerveWeakTransport

/-!
# 元の空語の対角 augmentation の弱同値性

概要：元の固定端点と全単体作用素を保持する。
方針：一頂点の一意性と実際の相対関手・対角比較を使う。
規約：通常の hammock augmentation の弱同値性を仮定しない。
使われ方：DK5.7の全語の帰納基底。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.Hammock.FixedObjectDiagram
open CategoryTheory SerrePositivity.InfinityCategories
variable (D : SimplicialObject _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u})
  (p : (i : SimplexCategoryᵒᵖ) → C.category → (D.obj i).category)
  (hp : ∀ {i j : SimplexCategoryᵒᵖ} (θ : i ⟶ j) (X : C.category),
    (D.map θ).functor.obj (p i X) = p j X)
  (A : D ⟶ (Functor.const SimplexCategoryᵒᵖ).obj C)
  (ha : ∀ i X, (A.app i).functor.obj (p i X) = X)
lemma wordDiagonalAugmentation_empty_weak
    (hA : ∀ i, Function.Injective (A.app i).functor.obj) (X Y : C.category) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.wordDiagonalAugmentation D C p hp A ha X Y).app _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.empty) := by
  have hd := DoubleSimplicial.diagonalFunctor_map_weak
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphWordAugmentation D C p hp A ha X Y).app _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.empty) (by
      intro n
      have := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.empty_fixed_isEquivalence (A.app n) (ha n X) (ha n Y) (hA n)
      exact nerveMap_equivalence_isWeakHomotopyEquivalence
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor.fixedFunctor (w := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.empty) (A.app n) (ha n X) (ha n Y)).asEquivalence)
  exact hd.comp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.wordDiagonalTargetIso C X Y).app _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.empty)).isWeakHomotopyEquivalence
end SerrePositivity.EInfinity.Hammock.FixedObjectDiagram
