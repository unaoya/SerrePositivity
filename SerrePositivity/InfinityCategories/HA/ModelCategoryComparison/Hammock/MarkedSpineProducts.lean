module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MarkedSpineSimplex
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.WeakTensor
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.WeakIndexedSum

/-!
# 元の非指定生成列に沿う有限個の指定因子の直積

概要：元の列ごとに指定 Hom の有限直積を作り、全列の依存和へ束ねる。
方針：列の先頭で元の二項直積を取り、比較射も同じ列で再帰する。
規約：長さ零には元の終端因子を置き、元の全端点と生成矢を保持する。
使われ方：元の hammock の自由積分解の全 Hom の弱比較。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine
open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.SerrePositivity.InfinityCategories

variable {C : Type u} [Category.{u} C] (W : MorphismProperty C)

def products (F : Paths C → Paths C → SSet.{u}) (Y : Paths C) :
    Paths C → List (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.Index W) → SSet.{u}
  | X, [] => F X Y
  | X, g :: gs => F X g.val.left ⊗ products F Y g.val.right gs

def productsMap {F G : Paths C → Paths C → SSet.{u}} (η : ∀ X Y, F X Y ⟶ G X Y)
    (Y : Paths C) : ∀ X gs, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.products W F Y X gs ⟶ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.products W G Y X gs
  | X, [] => η X Y
  | X, g :: gs => η X g.val.left ⊗ₘ productsMap η Y g.val.right gs

lemma productsMap_weak {F G : Paths C → Paths C → SSet.{u}}
    (η : ∀ X Y, F X Y ⟶ G X Y) (hη : ∀ X Y, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (η X Y))
    (Y X : Paths C) (gs : List (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.Index W)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.productsMap W η Y X gs) := by
  induction gs generalizing X with
  | nil => exact hη X Y
  | cons g gs ih => exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.weakTensor (hη X g.val.left) (ih g.val.right)

def sumProducts (F : Paths C → Paths C → SSet.{u}) (Y X : Paths C) : SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.IndexedSum.space (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.products W F Y X)

def sumProductsMap {F G : Paths C → Paths C → SSet.{u}} (η : ∀ X Y, F X Y ⟶ G X Y)
    (Y X : Paths C) : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.sumProducts W F Y X ⟶ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.sumProducts W G Y X :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.IndexedSum.map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.productsMap W η Y X)

lemma sumProductsMap_weak {F G : Paths C → Paths C → SSet.{u}}
    (η : ∀ X Y, F X Y ⟶ G X Y) (hη : ∀ X Y, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (η X Y))
    (Y X : Paths C) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.sumProductsMap W η Y X) :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.IndexedSum.map_weak _ (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.productsMap_weak W η hη Y X)

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine
