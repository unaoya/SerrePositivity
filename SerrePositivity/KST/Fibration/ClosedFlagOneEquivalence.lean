module
public import SerrePositivity.KST.Fibration.ClosedTailMultiStep

/-!
概要：一辺の元の P 相対旗と、元の P cofiber を持つ矢印模型の完全比較。
方針：全旗条件と一辺条件の同値を元の全部分圏制限へ代入する。
規約：同じ実恒等辺制限を使い、商や核表示を導入しない。
使われ方：有限旗の共通帰納の初段。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Fibration
open Relative

/-- 概要：元の一辺全旗条件は同じ元の矢印の P cofiber 条件そのもの。
方針：同じ実図式の wide への因子分解を両条件の共通表示にする。
規約：退化辺も含む。使われ方：一辺の元の完全比較の全境界持ち上げ。 -/
theorem closedFlagOne_predicate {B : StableModel.{u}} (P : ClosedStablePredicate B)
    (v : ((ihom (Δ[1] : SSet.{u})).obj B.carrier) _⦋0⦌) :
    (closedFlagStablePredicate P ⦋1⦌).predicate v ↔ (closedArrowPredicate P).predicate v := by
  let f := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (Δ[1] : SSet.{u}) B.carrier).symm v
  have hv : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f = v := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).apply_symm_apply v
  have h := (closedFlagStablePredicate_iff P ⦋1⦌ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f)).trans
    ((closedFlag_factor_iff P 1 f).trans (closedArrow_factor_iff P f).symm)
  simpa only [hv] using h

/-- 概要：一辺の元の旗比較は全境界を持ち上げる。
方針：同じ恒等制限と正確な頂点逆像の全部分圏補題。
規約：ModelCategory 仮定なし。使われ方：実完全同値と加法性の接続。 -/
instance closedFlagOne_trivialKan {B : StableModel.{u}} (P : ClosedStablePredicate B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (closedFlagEdge P (𝟙 ⦋1⦌)).val := by
  have hi : (pre (stdSimplex.map (𝟙 ⦋1⦌))).app B.carrier =
      𝟙 ((ihom (Δ[1] : SSet.{u})).obj B.carrier) := by
    rw [CategoryTheory.Functor.map_id, pre_id, NatTrans.id_app]
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (diagramRestrictionMap (flagAmbient B) (𝟙 ⦋1⦌)).val := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration ((pre (stdSimplex.map (𝟙 ⦋1⦌))).app B.carrier)
    rw [hi]
    infer_instance
  apply fullPredicateMap_trivialKanFibration
  intro v
  change (closedFlagStablePredicate P ⦋1⦌).predicate v ↔
    (closedArrowPredicate P).predicate
      (((pre (stdSimplex.map (𝟙 ⦋1⦌))).app B.carrier).app (Opposite.op ⦋0⦌) v)
  simpa only [hi, NatTrans.id_app, CategoryTheory.id_apply] using closedFlagOne_predicate P v

/-- 概要：元の一辺の旗制限を順射とする実完全同値。
方針：同じ trivial Kan 射の実完全同値を使う。
規約：順射を変更しない。使われ方：有限旗初段の元の実比較。 -/
def closedFlagOneEquivalence {B : StableModel.{u}} (P : ClosedStablePredicate B) :
    StableModelEquivalence (closedFlagModel P ⦋1⦌) (closedArrowModel P) :=
  stableTrivialEquivalence (closedFlagEdge P (𝟙 ⦋1⦌)).val

end SerrePositivity.KST.Fibration
