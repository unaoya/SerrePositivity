module
public import SerrePositivity.KST.Fibration.WeakStringTwoCriterion
public import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits

/-! # 接続した二つの W 辺の全図式圏

内二ホーン上の実図式に二つの元の短辺の W 条件を課す。
二条件は完全な制限による安定閉条件の交わりであり、合成の選択は含めない。
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

/-- 任意の添字の射による安定な図式圏の完全な制限。 -/
def ambientDiagramRestriction (B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) {K L : SSet.{u}} (f : K ⟶ L) :
    ambientDiagramModel L B ⟶ ambientDiagramModel K B :=
  ⟨(pre f).app B.obj, (pre_preservesSConstructionData f).toCofiberData⟩

/-- 接続した二辺が共に W である安定閉条件。 -/
def composableWeakArrowPredicate {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    ClosedStablePredicate (ambientDiagramModel (Λ[2, 1] : SSet.{u}) B) :=
  ((weakArrowClosedPredicate q).comap (ambientDiagramRestriction B horn₂₁.ι₀₁)).inter
    ((weakArrowClosedPredicate q).comap (ambientDiagramRestriction B horn₂₁.ι₁₂))

/-- 条件は元の二つの辺の W 判定を厳密に保持する。 -/
lemma composableWeakArrowPredicate_iff {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    (v : ((ihom (Λ[2, 1] : SSet.{u})).obj B.obj) _⦋0⦌) :
    (composableWeakArrowPredicate q).predicate v ↔
      weakArrowPredicate q (((pre horn₂₁.ι₀₁).app B.obj).app (Opposite.op ⦋0⦌) v) ∧
      weakArrowPredicate q (((pre horn₂₁.ι₁₂).app B.obj).app (Opposite.op ⦋0⦌) v) :=
  and_congr (weakArrowClosedPredicate_iff q _) (weakArrowClosedPredicate_iff q _)

/-- 合成の選択を持たない、接続した二つの W 辺の安定な図式圏。 -/
def composableWeakArrowModel {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) : StableModel.{u} :=
  closedStableModel (composableWeakArrowPredicate q)

/-- 二単体の W 条件は、内ホーンへの制限後の二短辺条件を正確に反映する。 -/
lemma weakStringTwoPredicate_iff_horn {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    (v : ((ihom (Δ[2] : SSet.{u})).obj B.obj) _⦋0⦌) :
    weakStringPredicate q ⦋2⦌ v ↔ (composableWeakArrowPredicate q).predicate
      (((pre (horn 2 1).ι).app B.obj).app (Opposite.op ⦋0⦌) v) := by
  rw [composableWeakArrowPredicate_iff, weakStringTwoPredicate_iff_shortEdges]
  have h₀ : (pre (horn 2 1).ι).app B.obj ≫ (pre horn₂₁.ι₀₁).app B.obj =
      (pre (stdSimplex.δ (2 : Fin 3))).app B.obj := by
    rw [← NatTrans.comp_app, ← pre_map, horn.ι_ι]
  have h₁ : (pre (horn 2 1).ι).app B.obj ≫ (pre horn₂₁.ι₁₂).app B.obj =
      (pre (stdSimplex.δ (0 : Fin 3))).app B.obj := by
    rw [← NatTrans.comp_app, ← pre_map, horn.ι_ι]
  rw [← h₀, ← h₁]
  rfl

end SerrePositivity.KST.Fibration
