module
public import SerrePositivity.KST.Fibration.TailWeakMultiStep

/-! # 元の長い W 列から先行列と最後の核値 cofiber への反復比較 -/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration

/-- 元の長い W 列から、元の先行列と最後の核値 cofiber を順序を保って取る射対。 -/
def weakStringTailMultiStep {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (n r : ℕ) :
    (multiRealizationFunctor r).obj (weakStringModel q ⦋n + 2⦌) ⟶
      (multiRealizationFunctor r).obj (weakStringModel q ⦋n + 1⦌) ⊗
        (multiRealizationFunctor r).obj (closedStableModel (kernelClosedPredicate q)) :=
  lift ((multiRealizationFunctor r).map
      ((weakStringTailEquivalence q n).hom ≫ tailWeakPrefixExact q n))
    ((multiRealizationFunctor r).map
      ((weakStringTailEquivalence q n).hom ≫ tailWeakCofiberExact q n))

/-- 同じ二成分は、元の貼り合わせへの制限とそこでの相対 cofiber 比較の合成。 -/
lemma weakStringTailMultiStep_factor {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (n r : ℕ) :
    (multiRealizationFunctor r).map (weakStringTailEquivalence q n).hom ≫
      tailWeakMultiStep q n r = weakStringTailMultiStep q n r := by
  unfold tailWeakMultiStep weakStringTailMultiStep
  rw [comp_lift, ← Functor.map_comp, ← Functor.map_comp]

/-- 元の長い W 列から先行列と最後の核値 cofiber への比較は全正有限反復で局所化同型。 -/
theorem weakStringTailMultiStep_localized_isIso {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (n r : ℕ) :
    IsIso (AnodyneHomotopy.anodyneQ.map (weakStringTailMultiStep q n (r + 1))) := by
  have := weakStringTail_multiRealization_localized_isIso q n r
  have := tailWeakMultiStep_localized_isIso q n r
  rw [← weakStringTailMultiStep_factor, Functor.map_comp]
  infer_instance

end SerrePositivity.KST.Fibration
