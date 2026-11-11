module
public import SerrePositivity.KST.Fibration.StandardTailCoordinates
public import SerrePositivity.KST.Fibration.WeakStringTailComponents
public import SerrePositivity.KST.Fibration.WeakStringTailMultiStep

/-! # 元の長い列の先行面と最後の連続 cofiber の厳密な回収 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Fibration

/-- 元の切断の先行成分は、既存の単体的対象の最後の面射そのもの。 -/
lemma weakStringTail_prefix_exact {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (n : ℕ) :
    (weakStringTailEquivalence q n).hom ≫ tailWeakPrefixExact q n =
      weakStringExactMap q (SimplexCategory.δ (Fin.last (n + 2))) := by
  apply Subtype.ext
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _
    (weakStringPredicate q ⦋n + 1⦌)).ι).1
  change ((weakStringTailEquivalence q n).hom.val ≫ (tailWeakPrefixExact q n).val) ≫ _ = _
  rw [Category.assoc, weakStringTail_prefix_ambient, standardTailPrefix_inclusion]
  exact (weakStringMap_ι q _).symm

/-- 元の切断の辺成分は、既存の最後の連続辺そのもの。 -/
lemma weakStringTail_edge_exact {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (n : ℕ) :
    (weakStringTailEquivalence q n).hom ≫ tailWeakEdgeExact q n =
      weakStringEdgeExact q (consecutiveWeakStringEdge (n + 2) (Fin.last (n + 1))) := by
  apply Subtype.ext
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (weakArrowPredicate q)).ι).1
  change ((weakStringTailEquivalence q n).hom.val ≫ (tailWeakEdgeExact q n).val) ≫ _ = _
  rw [Category.assoc, weakStringTail_edge_ambient, standardTailEdge_eq_consecutive]
  exact (weakStringEdgeMap_ι q _).symm

/-- 同じ切断の核値 cofiber は、既存の最後の連続辺の共通 cofiber 補完そのもの。 -/
lemma weakStringTail_cofiber_exact {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (n : ℕ) :
    (weakStringTailEquivalence q n).hom ≫ tailWeakCofiberExact q n =
      weakStringKernelCofiber q (consecutiveWeakStringEdge (n + 2) (Fin.last (n + 1))) := by
  unfold tailWeakCofiberExact weakStringKernelCofiber weakStringCofiberExact
  rw [← Category.assoc, ← Category.assoc, weakStringTail_edge_exact, Category.assoc]

/-- 全反復で元の先行面と最後の連続 cofiber の射対を厳密に回収する。 -/
lemma weakStringTailMultiStep_canonical {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (n r : ℕ) :
    weakStringTailMultiStep q n r =
      lift ((multiRealizationFunctor r).map
        (weakStringExactMap q (SimplexCategory.δ (Fin.last (n + 2)))))
        (weakStringCofiberMultiMap q
          (consecutiveWeakStringEdge (n + 2) (Fin.last (n + 1))) r) := by
  unfold weakStringTailMultiStep
  rw [weakStringTail_prefix_exact, weakStringTail_cofiber_exact]
  rfl

end SerrePositivity.KST.Fibration
