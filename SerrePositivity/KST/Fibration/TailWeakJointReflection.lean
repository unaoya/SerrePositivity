module
public import SerrePositivity.KST.Fibration.TailWeakPullback
public import SerrePositivity.KST.Fibration.ReindexJointReflection
public import SerrePositivity.KST.Fibration.FullSubcomplexJointReflection
public import SerrePositivity.KST.Fibration.WeakArrowAmbientExact
public import Mathlib.CategoryTheory.Limits.Types.Pushouts

/-! # 先行 W 列と最後の W 辺の両射影による実普遍性の共同反映 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Fibration

/-- 元の貼り合わせの全頂点は先行単体または最後の辺に含まれる。 -/
lemma standardTail_vertex_cover (n : ℕ)
    (v : (tailAttachment (Δ[n] : SSet.{u}) : SSet.{u}) _⦋0⦌) :
    (∃ a, (standardTailPrefix n).app (Opposite.op ⦋0⦌) a = v) ∨
      ∃ a, (tailAttachmentEdge (Δ[n] : SSet.{u})).app (Opposite.op ⦋0⦌) a = v := by
  exact (Types.eq_or_eq_of_isPushout ((standardTail_isPushout.{u} n).map
    ((evaluation SimplexCategoryᵒᵖ (Type u)).obj (Opposite.op ⦋0⦌))) v).symm

/-- 元の先行列と最後の辺は、貼り合わせ図式圏の零対象・実押し出しを共同で反映する。 -/
lemma tailWeak_jointReflection {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (n : ℕ) :
    JointlyReflectsSData (tailWeakPrefixExact q n).val (tailWeakEdgeExact q n).val := by
  apply (reindex_jointReflection (standardTailPrefix n) (tailAttachmentEdge (Δ[n] : SSet.{u}))
    (standardTail_vertex_cover n) (sInputModel B)).fullSubcomplex
    (tailWeakPredicate q n).predicate (weakStringPredicate q ⦋n + 1⦌) (weakArrowPredicate q)
    (p' := (tailWeakPrefixExact q n).val) (q' := (tailWeakEdgeExact q n).val) rfl rfl
  · exact stableModelHom_preservesSConstructionData
      (closedStableInclusion (weakStringClosedPredicate q ⦋n + 1⦌))
  · exact stableModelHom_preservesSConstructionData (weakArrowAmbientInclusion q)

end SerrePositivity.KST.Fibration
