module
public import SerrePositivity.KST.Fibration.WeakStringsSimplicial
public import SerrePositivity.KST.Fibration.WeakArrowClosedPredicate

/-! # 全有限 W 列の安定性

各実辺への制限で W 辺の閉じた安定条件を引き戻し、全ての辺で交差する。
この条件を元の全合成辺の可逆性と同定し、W 列図式圏の安定性を導く。
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

/-- 標準単体の再添字は、元の図式の完全な制限である。 -/
def diagramRestrictionMap (B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) {m n : SimplexCategory} (θ : m ⟶ n) :
    ambientDiagramModel (stdSimplex.obj n) B ⟶ ambientDiagramModel (stdSimplex.obj m) B :=
  ⟨(pre (stdSimplex.map θ)).app B.obj,
    (pre_preservesSConstructionData (stdSimplex.map θ)).toCofiberData⟩

/-- 全合成辺の可逆性は、各辺に制限した元の W 辺条件と一致する。 -/
lemma weakStringPredicate_iff_restrictions {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (n : SimplexCategory)
    (v : ((ihom (stdSimplex.obj n)).obj B.obj) _⦋0⦌) :
    weakStringPredicate q n v ↔ ∀ α : ⦋1⦌ ⟶ n,
      weakArrowPredicate q (((pre (stdSimplex.map α)).app B.obj).app (Opposite.op ⦋0⦌) v) := by
  change (∀ α : ⦋1⦌ ⟶ n, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (C.obj.map α.op (q.hom.app _ (simplexVertexValue n v))))) ↔ _
  apply forall_congr'
  intro α
  unfold weakArrowPredicate
  have hs := simplexVertexValue_reindex α v
  change arrowVertexSimplex
    (((pre (stdSimplex.map α)).app B.obj).app (Opposite.op ⦋0⦌) v) =
      B.obj.map α.op (simplexVertexValue n v) at hs
  rw [hs, ← NatTrans.naturality_apply]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr
    (e := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (B.obj.map α.op (simplexVertexValue n v))).map
      ((truncation 2).map q.hom))
    (f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (q.hom.app _ (B.obj.map α.op (simplexVertexValue n v)))) rfl).symm

/-- 全ての辺への制限で W 条件を課す、実関手圏上の閉じた安定条件。 -/
def weakStringClosedPredicate {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    (n : SimplexCategory) : ClosedStablePredicate (ambientDiagramModel (stdSimplex.obj n) B) := by
  let P (α : ⦋1⦌ ⟶ n) := (weakArrowClosedPredicate q).comap (diagramRestrictionMap B α)
  let R : ClosedStablePredicate (ambientDiagramModel (stdSimplex.obj n) B) := {
    predicate := fun v => ∀ α, (P α).predicate v
    of_iso := fun hx e α => (P α).of_iso (hx α) e
    zero_mem := fun hz α => (P α).zero_mem hz
    pushout_mem := fun F hF h00 h10 h01 α =>
      (P α).pushout_mem F hF (h00 α) (h10 α) (h01 α)
    pullback_mem := fun F hF h10 h01 h11 α =>
      (P α).pullback_mem F hF (h10 α) (h01 α) (h11 α) }
  have he (v) : R.predicate v ↔ weakStringPredicate q n v :=
    (forall_congr' (fun _ => weakArrowClosedPredicate_iff q _)).trans
      (weakStringPredicate_iff_restrictions q n v).symm
  exact {
    predicate := weakStringPredicate q n
    of_iso := fun hx e => (he _).1 (R.of_iso ((he _).2 hx) e)
    zero_mem := fun hz => (he _).1 (R.zero_mem hz)
    pushout_mem := fun F hF h00 h10 h01 => (he _).1
      (R.pushout_mem F hF ((he _).2 h00) ((he _).2 h10) ((he _).2 h01))
    pullback_mem := fun F hF h10 h01 h11 => (he _).1
      (R.pullback_mem F hF ((he _).2 h10) ((he _).2 h01) ((he _).2 h11)) }

/-- 構成した安定閉性条件は元の W 列の条件であり、cofiber の選択に依存しない。 -/
lemma weakStringClosedPredicate_iff {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    (n : SimplexCategory) (v : ((ihom (stdSimplex.obj n)).obj B.obj) _⦋0⦌) :
    (weakStringClosedPredicate q n).predicate v ↔ weakStringPredicate q n v := Iff.rfl

/-- 元の W 列図式圏は、構成した閉じた安定部分圏そのものである。 -/
lemma weakStringCategory_eq_closed {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    (n : SimplexCategory) :
    weakStringCategory q n = closedSubcategory (weakStringClosedPredicate q n) := rfl

/-- 全有限 W 列の図式圏は、安定性を仮定せず実際に安定である。 -/
instance weakStringCategory_isStable {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    (n : SimplexCategory) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable (weakStringCategory q n) :=
  inferInstanceAs (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable (closedSubcategory (weakStringClosedPredicate q n)))

/-- 同じ W 列の図式圏を K-1 の安定な入力として保持する。 -/
def weakStringModel {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    (n : SimplexCategory) : StableModel.{u} where
  carrier := weakStringCategory q n
  quasicategory := inferInstance
  stable := inferInstance

end SerrePositivity.KST.Fibration
