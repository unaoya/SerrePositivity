module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroCornerSquareSpan

/-!
概要：零終点 span の可縮性と、固定した実 span 上の零隅四角形の始対象。
方針：二辺の相対持ち上げ、全制限写像、同じ厳密 fiber の比較を接続する。
規約：安定性・余極限は仮定しない。使われ方：一般安定性判定の押し出し構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 零終点 span の族と同じ固定境界を保つ比較。 -/
lemma zeroCornerSquareSpan_source (X : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroCornerSquareSpan X ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroOuterSpanSource X = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroCornerSquareSource X := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroCornerSquareSpan, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroOuterSpanSource, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroOuterSpanLeftArrow,
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.zeroTargetArrowSource, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroCornerSquareSource]
  simp only [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι]
  simp only [Category.assoc, ← NatTrans.comp_app, ← pre_map,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary_bottomEdge, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.stable_pre_evaluateFunctorAt]
  rfl

/-- 零終点 span の族と同じ固定境界を保つ比較。 -/
lemma vertexFiberMap_kanEquivalenceLifting {E E' B : SSet.{u}}
    (p : E ⟶ B) (q : E' ⟶ B) (f : E ⟶ E') (hf : f ≫ q = p)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting f) (x : B _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p q f hf x) := by
  intro A D i hi he
  have := h i hi he
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.vertexFiberMap_hasLiftingProperty p q f hf x i

/-- 零終点 span の族と同じ固定境界を保つ比較。 -/
def zeroCornerSquareSpanSourceFiberMap (X : SSet.{u}) (x : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroCornerSquareSource X) x ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroOuterSpanSource X) x :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroCornerSquareSource X) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroOuterSpanSource X)
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroCornerSquareSpan X) (zeroCornerSquareSpan_source X) x

/-- 零終点 span の族と同じ固定境界を保つ比較。 -/
lemma zeroCornerSquareSpanSourceFiberMap_kanEquivalenceLifting
    (X : SSet.{u}) [Quasicategory X] (x : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting (zeroCornerSquareSpanSourceFiberMap X x) :=
  vertexFiberMap_kanEquivalenceLifting _ _ _ _
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroCornerSquareSpan_kanEquivalenceLifting X) x

/-- 零終点 span の族と同じ固定境界を保つ比較。 -/
instance zeroCornerSquareSourceFiber_quasicategory (X : SSet.{u}) [Quasicategory X]
    (x : X _⦋0⦌) : Quasicategory (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroCornerSquareSource X) x) := by
  let q := pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction (horn 2 2 : SSet.{u}) X)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom (horn 2 2 : SSet.{u})).obj X)
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsZeroOuterCospanVertex).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.coneApexEvaluation (horn 2 2 : SSet.{u}) X
  let f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroCornerSquareSource X) q (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroCornerSquareConeIso X).hom
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroCornerSquareConeIso_source X) x
  have : IsIso f := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.vertexFiberMap_isIso _ _ _ _ _
  have : Quasicategory (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber q x) := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.coneInputSourceFiber_quasicategory _ x
  exact quasicategory_of_innerFibration f
end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
