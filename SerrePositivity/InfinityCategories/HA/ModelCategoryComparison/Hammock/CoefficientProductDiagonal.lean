module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.CoefficientProductRelative
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DoubleSimplicialDiagonal
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.WeakTensor

/-!
# 元の係数積の対角 nerve と弱比較

概要：元の積圏の射列を二つの射列へ戻し、同じ対角比較の弱同値性を証明する。
方針：全単体の積と射影の厳密な往復、元の写像との正方形を使う。
規約：各次数の比較射の弱同値性は仮定せず、両対角の弱同値性だけを入力する。
使われ方：混合二方向の係数積の対角比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.CoefficientProduct
open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.SerrePositivity.InfinityCategories
variable (P Q : SimplicialObject Cat.{u, u})
def diagonalNerveIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalFunctor.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.CoefficientProduct.diagram P Q ⋙ nerveFunctor) ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalFunctor.obj (P ⋙ nerveFunctor) ⊗
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalFunctor.obj (Q ⋙ nerveFunctor) where
  hom :=
    { app n := ↾fun σ => (σ ⋙ CategoryTheory.Prod.fst (P.obj n) (Q.obj n),
        σ ⋙ CategoryTheory.Prod.snd (P.obj n) (Q.obj n))
      naturality n m θ := by
        apply ConcreteCategory.hom_ext
        intro σ
        rfl }
  inv :=
    { app n := ↾fun p => p.1.prod' p.2
      naturality n m θ := by
        apply ConcreteCategory.hom_ext
        intro p
        rfl }
  hom_inv_id := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro σ
    rfl
  inv_hom_id := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro p
    rfl
variable {P Q} {P' Q' : SimplicialObject Cat.{u, u}}
  (α : P ⟶ P') (β : Q ⟶ Q')
lemma diagonalNerveIso_naturality :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalFunctor.map
        (Functor.whiskerRight (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.change (𝟭 _) α β) nerveFunctor) ≫
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.CoefficientProduct.diagonalNerveIso P' Q').hom =
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.CoefficientProduct.diagonalNerveIso P Q).hom ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalFunctor.map (Functor.whiskerRight α nerveFunctor) ⊗ₘ
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalFunctor.map (Functor.whiskerRight β nerveFunctor)) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro σ
  rfl
lemma diagonalMap_weak
    (hα : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalFunctor.map (Functor.whiskerRight α nerveFunctor)))
    (hβ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalFunctor.map (Functor.whiskerRight β nerveFunctor))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalFunctor.map
      (Functor.whiskerRight (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.change (𝟭 _) α β) nerveFunctor)) := by
  have h := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.CoefficientProduct.diagonalNerveIso P Q)).isWeakHomotopyEquivalence.comp (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.weakTensor hα hβ)
  rw [← _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.CoefficientProduct.diagonalNerveIso_naturality] at h
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.CoefficientProduct.diagonalNerveIso P' Q')).isWeakHomotopyEquivalence.cancel_right h
end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.CoefficientProduct
