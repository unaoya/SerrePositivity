module
public import SerrePositivity.KST.Fibration.TailWeakModel
public import SerrePositivity.KST.Fibration.FullPredicatePullback
public import SerrePositivity.KST.Fibration.WeakArrowEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.PrecompositionLifting

/-! # 先行 W 列と最後の W 辺の元の共有端点上の厳密な引き戻し -/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Fibration

/-- 貼り合わせから元の先行 W 列を抽出する。 -/
def tailWeakPrefixMap {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (n : ℕ) :
    (tailWeakModel q n).carrier ⟶ (weakStringModel q ⦋n + 1⦌).carrier :=
  fullPredicateMap ((pre (standardTailPrefix n)).app B.obj) (tailWeakPredicate q n).predicate
    (weakStringPredicate q ⦋n + 1⦌) (fun v hv => ((tailWeakPredicate_iff q n v).1 hv).1)

/-- 貼り合わせから元の最後の実 W 辺を抽出する。 -/
def tailWeakEdgeMap {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (n : ℕ) :
    (tailWeakModel q n).carrier ⟶ weakArrowCategory q :=
  fullPredicateMap ((pre (tailAttachmentEdge (Δ[n] : SSet.{u}))).app B.obj)
    (tailWeakPredicate q n).predicate (weakArrowPredicate q)
    (fun v hv => ((tailWeakPredicate_iff q n v).1 hv).2)

/-- 元の先行列と最後の W 辺を、元の共有端点図式に沿って貼る厳密引き戻し。 -/
theorem tailWeak_isPullback {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (n : ℕ) :
    IsPullback (tailWeakPrefixMap q n) (tailWeakEdgeMap q n)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (weakStringPredicate q ⦋n + 1⦌)).ι ≫
        (pre (standardTailEndpoint n)).app B.obj)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (weakArrowPredicate q)).ι ≫
        (pre (stdSimplex.δ (1 : Fin 2))).app B.obj) :=
  isPullback_fullPredicates (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isPullback_pre_of_isPushout (standardTail_isPushout n) B.obj)
    (tailWeakPredicate q n).predicate (weakStringPredicate q ⦋n + 1⦌) (weakArrowPredicate q)
    (tailWeakPredicate_iff q n)

/-- 元の先行 W 列への制限は完全。 -/
def tailWeakPrefixExact {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (n : ℕ) :
    tailWeakModel q n ⟶ weakStringModel q ⦋n + 1⦌ :=
  ⟨tailWeakPrefixMap q n, by
    apply preservesCofiberData_fullSubcomplex_of_comp (weakStringPredicate q ⦋n + 1⦌)
    exact (closedStableInclusion (tailWeakPredicate q n)).property.comp
      (ambientDiagramRestriction B (standardTailPrefix n)).property⟩

/-- 元の最後の W 辺への制限も完全。 -/
def tailWeakEdgeExact {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (n : ℕ) :
    tailWeakModel q n ⟶ weakArrowModel q :=
  ⟨tailWeakEdgeMap q n, by
    apply preservesCofiberData_fullSubcomplex_of_comp (weakArrowPredicate q)
    exact (closedStableInclusion (tailWeakPredicate q n)).property.comp
      (ambientDiagramRestriction B (tailAttachmentEdge (Δ[n] : SSet.{u}))).property⟩

end SerrePositivity.KST.Fibration
