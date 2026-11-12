module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroCornerSquareSpanSourceFiber
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LoopConeChoiceModel

/-!
概要：元の普遍 loop 錐の指定点の始対象性と、同じ零隅四角形への移送。
方針：固定 cospan の終対象の自己比較と、実 classifier・選択忘却を接続する。
規約：最後の全四角形図式を厳密に保つ。使われ方：同じ loop 四角形の押し出し性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 元の普遍 loop 錐の同じ指定点と四角形を保つ比較。 -/
def loopConeZeroCornerForget (X : SSet.{u}) [Quasicategory X] :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeObjects X ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroCornerSquares X :=
  (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeChoiceIso X).hom ≫
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.coneChoiceForget (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom (horn 2 2 : SSet.{u})).obj X)
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsZeroOuterCospanVertex).ι ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroCornerSquareConeIso X).inv

/-- 元の普遍 loop 錐の同じ指定点と四角形を保つ比較。 -/
lemma loopConeZeroCornerForget_source (X : SSet.{u}) [Quasicategory X] :
    loopConeZeroCornerForget X ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroCornerSquareSource X = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeObjectSource X := by
  let p := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom (horn 2 2 : SSet.{u})).obj X)
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsZeroOuterCospanVertex).ι
  let q := pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction (horn 2 2 : SSet.{u}) X) p ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.coneApexEvaluation (horn 2 2 : SSet.{u}) X
  have hi : (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroCornerSquareConeIso X).inv ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroCornerSquareSource X = q := by
    rw [← _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroCornerSquareConeIso_source, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  change ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeChoiceIso X).hom ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.coneChoiceForget p ≫
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroCornerSquareConeIso X).inv) ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroCornerSquareSource X = _
  rw [Category.assoc, Category.assoc, hi]
  change (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeChoiceIso X).hom ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.coneChoiceForget p ≫
    pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction (horn 2 2 : SSet.{u}) X) p ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.coneApexEvaluation (horn 2 2 : SSet.{u}) X = _
  rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.coneChoiceForget p), _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.coneChoiceForget_diagram,
    ← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeChoiceIso_diagram]
  rfl

/-- 元の普遍 loop 錐の同じ指定点と四角形を保つ比較。 -/
lemma loopConeZeroCornerForget_trivialKanFibration (X : SSet.{u}) [Quasicategory X]
    [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits X] : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (loopConeZeroCornerForget X) := by
  have hp := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.coneChoiceForget_trivialKanFibration
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom (horn 2 2 : SSet.{u})).obj X)
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsZeroOuterCospanVertex).ι (fun p ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits.hasLimit p)
  dsimp only [loopConeZeroCornerForget]
  exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibrations.comp_mem _ _ (MorphismProperty.rlp_of_isIso _ _)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibrations.comp_mem _ _ hp.mem (MorphismProperty.rlp_of_isIso _ _))⟩

/-- 元の普遍 loop 錐の同じ指定点と四角形を保つ比較。 -/
def loopConeZeroCornerSourceFiberMap (X : SSet.{u}) [Quasicategory X] (x : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeObjectSource X) x ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroCornerSquareSource X) x :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeObjectSource X) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroCornerSquareSource X)
    (loopConeZeroCornerForget X) (loopConeZeroCornerForget_source X) x

/-- 元の普遍 loop 錐の同じ指定点と四角形を保つ比較。 -/
lemma loopConeZeroCornerSourceFiberMap_trivialKanFibration (X : SSet.{u})
    [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits X] (x : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (loopConeZeroCornerSourceFiberMap X x) := by
  have := loopConeZeroCornerForget_trivialKanFibration X
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.vertexFiberMap_trivialKanFibration _ _ _ _ _

/-- 元の普遍 loop 錐の同じ指定点と四角形を保つ比較。 -/
lemma loopConeZeroCornerSourceFiberMap_isQCatEquivalence (X : SSet.{u})
    [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits X] (x : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (loopConeZeroCornerSourceFiberMap X x) := by
  have := loopConeZeroCornerSourceFiberMap_trivialKanFibration X x
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration _
end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
