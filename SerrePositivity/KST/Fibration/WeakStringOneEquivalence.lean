module
public import SerrePositivity.KST.Fibration.WeakStringEdges

/-! # 一辺の W 列と既存の W 辺図式圏の元の比較同値 -/

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

/-- 一辺の元の辺抽出は全境界の持ち上げを保つ。 -/
instance weakStringOneEdge_trivialKanFibration {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (weakStringEdgeMap q (𝟙 ⦋1⦌)) := by
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration ((pre (stdSimplex.map (𝟙 ⦋1⦌))).app B.obj) := by
    rw [CategoryTheory.Functor.map_id, pre_id, NatTrans.id_app]
    infer_instance
  apply fullPredicateMap_trivialKanFibration
    ((pre (stdSimplex.map (𝟙 ⦋1⦌))).app B.obj)
  intro v
  rw [CategoryTheory.Functor.map_id, pre_id, NatTrans.id_app]
  exact weakStringPredicate_one_iff q v

/-- 同値の順射は元の一辺の抽出そのもので、完全な逆と coherent な比較を持つ。 -/
def weakStringOneArrowEquivalence {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    StableModelEquivalence (weakStringModel q ⦋1⦌) (weakArrowModel q) := by
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.qCatEquivalenceOfTrivialKanFibration (weakStringEdgeMap q (𝟙 ⦋1⦌))
  have hi := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_isQCatEquivalence e.symm.isQCatEquivalence
  exact {
    hom := weakStringEdgeExact q (𝟙 ⦋1⦌)
    inv := ⟨e.inv, hi.preservesZero, hi.preservesCofiber⟩
    homInvIso := e.homInvIso
    invHomIso := e.invHomIso }

end SerrePositivity.KST.Fibration
