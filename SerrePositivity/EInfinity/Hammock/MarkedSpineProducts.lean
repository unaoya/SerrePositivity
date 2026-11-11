module

public import SerrePositivity.EInfinity.Hammock.MarkedSpineSimplex
public import SerrePositivity.EInfinity.Hammock.WeakTensor
public import SerrePositivity.EInfinity.Hammock.WeakIndexedSum

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
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine
open CategoryTheory MonoidalCategory SerrePositivity.InfinityCategories

variable {C : Type u} [Category.{u} C] (W : MorphismProperty C)

def products (F : Paths C → Paths C → SSet.{u}) (Y : Paths C) :
    Paths C → List (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.Index W) → SSet.{u}
  | X, [] => F X Y
  | X, g :: gs => F X g.val.left ⊗ products F Y g.val.right gs

def productsMap {F G : Paths C → Paths C → SSet.{u}} (η : ∀ X Y, F X Y ⟶ G X Y)
    (Y : Paths C) : ∀ X gs, products W F Y X gs ⟶ products W G Y X gs
  | X, [] => η X Y
  | X, g :: gs => η X g.val.left ⊗ₘ productsMap η Y g.val.right gs

lemma productsMap_weak {F G : Paths C → Paths C → SSet.{u}}
    (η : ∀ X Y, F X Y ⟶ G X Y) (hη : ∀ X Y, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (η X Y))
    (Y X : Paths C) (gs : List (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.Index W)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (productsMap W η Y X gs) := by
  induction gs generalizing X with
  | nil => exact hη X Y
  | cons g gs ih => exact weakTensor (hη X g.val.left) (ih g.val.right)

def sumProducts (F : Paths C → Paths C → SSet.{u}) (Y X : Paths C) : SSet.{u} :=
  IndexedSum.space (products W F Y X)

def sumProductsMap {F G : Paths C → Paths C → SSet.{u}} (η : ∀ X Y, F X Y ⟶ G X Y)
    (Y X : Paths C) : sumProducts W F Y X ⟶ sumProducts W G Y X :=
  IndexedSum.map (productsMap W η Y X)

lemma sumProductsMap_weak {F G : Paths C → Paths C → SSet.{u}}
    (η : ∀ X Y, F X Y ⟶ G X Y) (hη : ∀ X Y, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (η X Y))
    (Y X : Paths C) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (sumProductsMap W η Y X) :=
  IndexedSum.map_weak _ (productsMap_weak W η hη Y X)

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine
