module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorDoubleConeFrontMap

/-!
概要：元の閉 augmentation の全斉次値は、二重 cone の任意作用素への制限と整合する。
方針：元の augmentation の零・後続分岐と、終端を除いた添字の回復を使う。
規約：同じ実 chain map の閉 cochain を保つ。使われ方：終端成分の自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.InfinityCategories
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (X Y : Complex A)

lemma normalizedTensorConeAugmentationClosed_reindex {n m : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n) (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (i : Fin (m + 2)) (k : ℤ) :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom ((_root_.SerrePositivity.ComplexLimits.complexToClosed A).map
      (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeAugmentationAt A X Y c (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom θ.toOrderHom i))) k)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom ((_root_.SerrePositivity.ComplexLimits.complexToClosed A).map
        (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeAugmentationAt A X Y
          ((SimplexCategory.toCat.map θ).toFunctor ⋙ c) i)) k) := by
  induction i using Fin.cases with
  | zero => rfl
  | succ i => rfl

lemma normalizedTensorDoubleConeTerminalValue_reindex {n m : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n) (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (i : Fin (m + 3)) (k : ℤ) (hi : i ≠ Fin.last (m + 2)) :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom ((_root_.SerrePositivity.ComplexLimits.complexToClosed A).map
      (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeAugmentationAt A X Y c
        ((Fin.last (n + 1)).predAboveOrderHom (_root_.SerrePositivity.ComplexLimits.doubleConeOrderHom θ i)))) k)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom ((_root_.SerrePositivity.ComplexLimits.complexToClosed A).map
        (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeAugmentationAt A X Y
          ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)
          ((Fin.last (m + 1)).predAboveOrderHom i))) k) := by
  have ht : ∀ a b : Fin (n + 2), a = b →
      HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom ((_root_.SerrePositivity.ComplexLimits.complexToClosed A).map
        (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeAugmentationAt A X Y c a)) k)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom ((_root_.SerrePositivity.ComplexLimits.complexToClosed A).map
          (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeAugmentationAt A X Y c b)) k) := by
    intro a b h
    subst b
    rfl
  exact (ht _ _ (_root_.SerrePositivity.ComplexLimits.doubleConeOrderHom_predAbove θ i hi)).trans
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeAugmentationClosed_reindex A X Y c θ _ k)

end SerrePositivity.ComplexLimits
