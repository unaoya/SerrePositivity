module
public import SerrePositivity.KST.Fibration.WeakStringTailEquivalence
public import SerrePositivity.KST.Fibration.TailWeakPullback

/-! # 元の全 W 列の切断が保持する先行列と最後の実辺 -/

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

/-- 制限の元の全貼り合わせ図式への包含は、同じ貼り合わせ包含による前合成。 -/
lemma weakStringTailRestriction_ι {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (n : ℕ) :
    weakStringTailRestriction q n ≫ (closedStableInclusion (tailWeakPredicate q n)).val =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (weakStringPredicate q ⦋n + 2⦌)).ι ≫
        (pre (standardTailInclusion n)).app B.obj := rfl

/-- 同じ先行列への射影は、元の長い単体図式の先行単体への制限を厳密に回収する。 -/
lemma weakStringTail_prefix_ambient {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (n : ℕ) :
    (weakStringTailEquivalence q n).hom.val ≫ (tailWeakPrefixExact q n).val ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (weakStringPredicate q ⦋n + 1⦌)).ι =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (weakStringPredicate q ⦋n + 2⦌)).ι ≫
          (pre (standardTailPrefix n ≫ standardTailInclusion n)).app B.obj := by
  have hp : (tailWeakPrefixExact q n).val ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (weakStringPredicate q ⦋n + 1⦌)).ι =
        (closedStableInclusion (tailWeakPredicate q n)).val ≫
          (pre (standardTailPrefix n)).app B.obj := rfl
  rw [hp, weakStringTailEquivalence_hom, ← Category.assoc, weakStringTailRestriction_ι,
    Category.assoc, ← NatTrans.comp_app, ← pre_map]

/-- 最後の実 W 辺への射影も、元の長い単体図式の同じ実辺への制限を回収する。 -/
lemma weakStringTail_edge_ambient {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (n : ℕ) :
    (weakStringTailEquivalence q n).hom.val ≫ (tailWeakEdgeExact q n).val ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (weakArrowPredicate q)).ι =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (weakStringPredicate q ⦋n + 2⦌)).ι ≫
          (pre (tailAttachmentEdge (Δ[n] : SSet.{u}) ≫ standardTailInclusion n)).app B.obj := by
  have he : (tailWeakEdgeExact q n).val ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (weakArrowPredicate q)).ι =
        (closedStableInclusion (tailWeakPredicate q n)).val ≫
          (pre (tailAttachmentEdge (Δ[n] : SSet.{u}))).app B.obj := rfl
  rw [he, weakStringTailEquivalence_hom, ← Category.assoc, weakStringTailRestriction_ι,
    Category.assoc, ← NatTrans.comp_app, ← pre_map]

end SerrePositivity.KST.Fibration
