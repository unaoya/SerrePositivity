module
public import SerrePositivity.KST.Fibration.StandardTailVertices
public import SerrePositivity.KST.Fibration.ComposableWeakArrows

/-! # 元の先行 W 列と最後の W 辺を貼り合わせた安定な全図式圏 -/

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

/-- 先行列の全辺と元の最後の辺の双方に W 条件を課す閉じた安定条件。 -/
def tailWeakPredicate {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (n : ℕ) :
    ClosedStablePredicate (ambientDiagramModel
      (tailAttachment (Δ[n] : SSet.{u}) : SSet.{u}) B) :=
  ((weakStringClosedPredicate q ⦋n + 1⦌).comap
    (ambientDiagramRestriction B (standardTailPrefix n))).inter
      ((weakArrowClosedPredicate q).comap
        (ambientDiagramRestriction B (tailAttachmentEdge (Δ[n] : SSet.{u}))))

/-- 閉じた条件は、元の先行 W 列と最後の実 W 辺の条件そのもの。 -/
lemma tailWeakPredicate_iff {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (n : ℕ)
    (v : ((ihom (tailAttachment (Δ[n] : SSet.{u}) : SSet.{u})).obj B.obj) _⦋0⦌) :
    (tailWeakPredicate q n).predicate v ↔
      weakStringPredicate q ⦋n + 1⦌
        (((pre (standardTailPrefix n)).app B.obj).app (Opposite.op ⦋0⦌) v) ∧
      weakArrowPredicate q
        (((pre (tailAttachmentEdge (Δ[n] : SSet.{u}))).app B.obj).app (Opposite.op ⦋0⦌) v) :=
  and_congr (weakStringClosedPredicate_iff q _ _) (weakArrowClosedPredicate_iff q _)

/-- 元の全貼り合わせ図式と全高次自然変換を保持する安定模型。 -/
def tailWeakModel {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (n : ℕ) : StableModel.{u} :=
  closedStableModel (tailWeakPredicate q n)

end SerrePositivity.KST.Fibration
