module
public import SerrePositivity.KST.Fibration.WeakStringTwoHornEquivalence
public import SerrePositivity.KST.Fibration.ComposableWeakArrowPullback

/-! # 二辺の切断比較の元の両成分

接続した二辺への制限は完全であり、元の二単体の同じ二短辺を厳密に回収する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Fibration

/-- 接続した二辺から最初の W 辺を取る完全関手。 -/
def composableWeakFirstExact {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    composableWeakArrowModel q ⟶ weakArrowModel q :=
  ⟨composableWeakFirstMap q, by
    apply preservesCofiberData_fullSubcomplex_of_comp (weakArrowPredicate q)
    rw [composableWeakFirstMap_ι]
    exact (closedStableInclusion (composableWeakArrowPredicate q)).property.comp
      (ambientDiagramRestriction B horn₂₁.ι₀₁).property⟩

/-- 接続した二辺から次の W 辺を取る完全関手。 -/
def composableWeakNextExact {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    composableWeakArrowModel q ⟶ weakArrowModel q :=
  ⟨composableWeakNextMap q, by
    apply preservesCofiberData_fullSubcomplex_of_comp (weakArrowPredicate q)
    rw [composableWeakNextMap_ι]
    exact (closedStableInclusion (composableWeakArrowPredicate q)).property.comp
      (ambientDiagramRestriction B horn₂₁.ι₁₂).property⟩

/-- 同値の第一成分は、元の二単体の第一短辺の抽出そのもの。 -/
lemma weakStringTwoHornExact_first {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    weakStringTwoHornExact q ≫ composableWeakFirstExact q =
      weakStringEdgeExact q (SimplexCategory.δ (2 : Fin 3)) := by
  apply Subtype.ext
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (weakArrowPredicate q)).ι).1
  change (weakStringTwoHornRestriction q ≫ composableWeakFirstMap q) ≫ _ =
    weakStringEdgeMap q (SimplexCategory.δ (2 : Fin 3)) ≫ _
  rw [Category.assoc, composableWeakFirstMap_ι, ← Category.assoc,
    weakStringTwoHornRestriction_ι, Category.assoc, weakStringEdgeMap_ι]
  congr 1

/-- 同値の第二成分も、元の二単体の第二短辺の抽出そのもの。 -/
lemma weakStringTwoHornExact_next {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    weakStringTwoHornExact q ≫ composableWeakNextExact q =
      weakStringEdgeExact q (SimplexCategory.δ (0 : Fin 3)) := by
  apply Subtype.ext
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (weakArrowPredicate q)).ι).1
  change (weakStringTwoHornRestriction q ≫ composableWeakNextMap q) ≫ _ =
    weakStringEdgeMap q (SimplexCategory.δ (0 : Fin 3)) ≫ _
  rw [Category.assoc, composableWeakNextMap_ι, ← Category.assoc,
    weakStringTwoHornRestriction_ι, Category.assoc, weakStringEdgeMap_ι]
  congr 1

end SerrePositivity.KST.Fibration
