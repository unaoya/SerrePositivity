module
public import SerrePositivity.KST.Fibration.WeakStringCofibers
public import SerrePositivity.KST.SConstruction.MultiRealization

/-! # 元の全合成辺の cofiber 実現射の再添字

元の共通 cofiber 完全関手の実現射と射対を構成する。
全ての面・退化との可換性は、八面体の選択に依存せず厳密に成立する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Fibration

/-- 元の指定合成辺の共通 cofiber 完全関手の反復実現射。 -/
def weakStringCofiberMultiMap {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    {n : SimplexCategory} (α : ⦋1⦌ ⟶ n) (r : ℕ) :
    (multiRealizationFunctor r).obj (weakStringModel q n) ⟶
      (multiRealizationFunctor r).obj (closedStableModel (kernelClosedPredicate q)) :=
  (multiRealizationFunctor r).map (weakStringKernelCofiber q α)

/-- 元の実現射は、面・退化を含む全ての再添字と厳密に可換する。 -/
lemma weakStringCofiberMultiMap_reindex {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    {m n : SimplexCategory} (θ : m ⟶ n) (α : ⦋1⦌ ⟶ m) (r : ℕ) :
    (multiRealizationFunctor r).map (weakStringExactMap q θ) ≫
      weakStringCofiberMultiMap q α r = weakStringCofiberMultiMap q (α ≫ θ) r := by
  change (multiRealizationFunctor r).map _ ≫ (multiRealizationFunctor r).map _ = _
  rw [← Functor.map_comp, weakStringKernelCofiber_reindex]
  rfl

/-- 同じ列の元の二つの合成辺の cofiber 実現射対。 -/
def weakStringCofiberMultiPair {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    {n : SimplexCategory} (α β : ⦋1⦌ ⟶ n) (r : ℕ) :
    (multiRealizationFunctor r).obj (weakStringModel q n) ⟶
      (multiRealizationFunctor r).obj (closedStableModel (kernelClosedPredicate q)) ⊗
        (multiRealizationFunctor r).obj (closedStableModel (kernelClosedPredicate q)) :=
  lift (weakStringCofiberMultiMap q α r) (weakStringCofiberMultiMap q β r)

/-- 元の二辺の射対も、全ての列の制限と厳密に可換する。 -/
lemma weakStringCofiberMultiPair_reindex {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    {m n : SimplexCategory} (θ : m ⟶ n) (α β : ⦋1⦌ ⟶ m) (r : ℕ) :
    (multiRealizationFunctor r).map (weakStringExactMap q θ) ≫
      weakStringCofiberMultiPair q α β r =
        weakStringCofiberMultiPair q (α ≫ θ) (β ≫ θ) r := by
  unfold weakStringCofiberMultiPair
  rw [comp_lift, weakStringCofiberMultiMap_reindex, weakStringCofiberMultiMap_reindex]

end SerrePositivity.KST.Fibration
