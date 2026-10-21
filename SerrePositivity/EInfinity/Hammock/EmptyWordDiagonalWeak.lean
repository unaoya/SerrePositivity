module

public import SerrePositivity.EInfinity.Hammock.RelativeEmptyZigzagEquivalence
public import SerrePositivity.EInfinity.Hammock.WordDiagonalAugmentation
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
open CategoryTheory SimplicialLocalization SerrePositivity.InfinityCategories
variable (D : SimplicialObject RelativeCategory.{u}) (C : RelativeCategory.{u})
  (p : (i : SimplexCategoryᵒᵖ) → C.category → (D.obj i).category)
  (hp : ∀ {i j : SimplexCategoryᵒᵖ} (θ : i ⟶ j) (X : C.category),
    (D.map θ).functor.obj (p i X) = p j X)
  (A : D ⟶ (Functor.const SimplexCategoryᵒᵖ).obj C)
  (ha : ∀ i X, (A.app i).functor.obj (p i X) = X)
lemma wordDiagonalAugmentation_empty_weak
    (hA : ∀ i, Function.Injective (A.app i).functor.obj) (X Y : C.category) :
    IsWeakHomotopyEquivalence ((wordDiagonalAugmentation D C p hp A ha X Y).app Word.empty) := by
  have hd := DoubleSimplicial.diagonalFunctor_map_weak
    ((graphWordAugmentation D C p hp A ha X Y).app Word.empty) (by
      intro n
      have := Zigzag.Relative.empty_fixed_isEquivalence (A.app n) (ha n X) (ha n Y) (hA n)
      exact nerveMap_equivalence_isWeakHomotopyEquivalence
        (Zigzag.Relative.fixedFunctor (w := Word.empty) (A.app n) (ha n X) (ha n Y)).asEquivalence)
  exact hd.comp (isPrecompositionEquivalence_of_iso
    ((wordDiagonalTargetIso C X Y).app Word.empty)).isWeakHomotopyEquivalence
end SerrePositivity.EInfinity.Hammock.FixedObjectDiagram
