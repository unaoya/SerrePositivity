module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.InitialEquivalence

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IdentityCocone
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.LeftFibrationInitialEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.CosliceTwistedArrowTarget
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TargetReconstruction
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.RightRepresentableTwistedArrowEquivalence

/-!
概要：Tw 全体の同じ復元射から、実際の Yoneda 前層の恒等点と評価を取る。
方針：元の反転 coslice の恒等点を、終点固定に制限した全体の復元射で送る。
規約：以前の別々に選んだ比較の評価点との一致は仮定しない。
使われ方：同じ全体の射の自然性を使い、c1 の fiber 輸送を twisted arrow の輸送へ移す。

対応節は Kerodon 8.3（Tag 03LZ）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.CanonicalYonedaUnstraighteningIdentity

attribute [local instance] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex_of_leftFibration

local instance {C : SSet.{u}} [Quasicategory C] : Quasicategory (C.op ⊗ C) :=
  quasicategory_of_innerFibration (fst C.op C)

local instance {C : SSet.{u}} [Quasicategory C] (y : C _⦋0⦌) :
    Quasicategory (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraightening (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity y)) :=
  quasicategory_of_innerFibration
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity y))

/-- 元の反転 coslice から終点固定の twisted arrow への比較も前合成同値。 -/
lemma cosliceToTwistedArrowTarget_isPrecompositionEquivalence
    {C : SSet.{u}} [Quasicategory C] (y : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceToTwistedArrowTarget y) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.rightRepresentableTwistedArrowMap_isPrecompositionEquivalence y
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalPointSliceOverOpIso y).hom.left ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceToTwistedArrowTarget y) at h
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso
    ((Over.forget C.op).mapIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalPointSliceOverOpIso y))).cancel_left h

/-- 全体の同じ復元射から取る、元の反転 coslice との比較。 -/
def canonicalYonedaCosliceComparison {C : SSet.{u}} [Quasicategory C] (y : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (SSet.yonedaEquiv.symm (SSet.opObjEquiv.symm y)) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraightening (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity y) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceToTwistedArrowTarget y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TargetReconstruction.twistedArrowTargetReconstruction y

/-- 同じ比較は元の反転した底を厳密に保つ。 -/
lemma canonicalYonedaCosliceComparison_projection
    {C : SSet.{u}} [Quasicategory C] (y : C _⦋0⦌) :
    canonicalYonedaCosliceComparison y ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity y) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm (SSet.opObjEquiv.symm y)) := by
  rw [canonicalYonedaCosliceComparison, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TargetReconstruction.twistedArrowTargetReconstruction_projection, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceToTwistedArrowTarget_projection]

/-- 同じ比較を全体へ戻すと、元の錐の比較と全体の復元射の合成そのもの。 -/
lemma canonicalYonedaCosliceComparison_global
    {C : SSet.{u}} [Quasicategory C] (y : C _⦋0⦌) :
    canonicalYonedaCosliceComparison y ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity y) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedArrowHomInfinity C)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedArrowTargetInclusion y)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity_eq_targetRestriction y).symm =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceOppositeTwistedArrowMap (SSet.yonedaEquiv.symm (SSet.opObjEquiv.symm y)) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityReconstruction (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection C) := by
  rw [canonicalYonedaCosliceComparison, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TargetReconstruction.twistedArrowTargetReconstruction_map,
    ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceToTwistedArrowTarget, pullback.lift_fst]

/-- 同じ coslice 比較は全空間で前合成同値。 -/
lemma canonicalYonedaCosliceComparison_isPrecompositionEquivalence
    {C : SSet.{u}} [Quasicategory C] (y : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (canonicalYonedaCosliceComparison y) :=
  (cosliceToTwistedArrowTarget_isPrecompositionEquivalence y).comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TargetReconstruction.twistedArrowTargetReconstruction_isPrecompositionEquivalence y)

/-- Tw 全体の同じ復元射を終点固定で読む、実際の Yoneda 前層内の恒等点。 -/
def canonicalYonedaUnstraighteningIdentity
    {C : SSet.{u}} [Quasicategory C] (y : C _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraightening (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity y)) _⦋0⦌ :=
  (canonicalYonedaCosliceComparison y).app (Opposite.op ⦋0⦌)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.cosliceIdentityCone (SSet.opObjEquiv.symm y))

/-- 恒等点の全体での像も、同じ Tw の恒等錐を元の復元射で送った点。 -/
lemma canonicalYonedaUnstraighteningIdentity_global
    {C : SSet.{u}} [Quasicategory C] (y : C _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity y) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedArrowHomInfinity C)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedArrowTargetInclusion y)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity_eq_targetRestriction y).symm).app
        (Opposite.op ⦋0⦌) (canonicalYonedaUnstraighteningIdentity y) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityReconstruction (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection C)).app (Opposite.op ⦋0⦌)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceOppositeTwistedArrowMap
        (SSet.yonedaEquiv.symm (SSet.opObjEquiv.symm y))).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.cosliceIdentityCone (SSet.opObjEquiv.symm y))) :=
  congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.cosliceIdentityCone (SSet.opObjEquiv.symm y))) (canonicalYonedaCosliceComparison_global y)

/-- 同じ恒等点の射影は、指定した元の頂点である。 -/
lemma canonicalYonedaUnstraighteningIdentity_projection
    {C : SSet.{u}} [Quasicategory C] (y : C _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity y)).app
      (Opposite.op ⦋0⦌) (canonicalYonedaUnstraighteningIdentity y) = SSet.opObjEquiv.symm y := by
  have h := congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.cosliceIdentityCone (SSet.opObjEquiv.symm y)))
    (canonicalYonedaCosliceComparison_projection y)
  exact h.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.cosliceIdentityCone_projection _)

/-- 全体から取った同じ恒等点は、実際の unstraightening 全空間の始対象。 -/
lemma canonicalYonedaUnstraighteningIdentity_isInitialVertex
    {C : SSet.{u}} [Quasicategory C] (y : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex (canonicalYonedaUnstraighteningIdentity y) := by
  have h := canonicalYonedaCosliceComparison_isPrecompositionEquivalence y
  exact h.isQCatEquivalence.choose.map_isInitialVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.cosliceIdentityCone_isInitialVertex _)

/-- 全体から取った同じ恒等点で、元の全相対 Hom を直接評価する。 -/
def canonicalYonedaUnstraighteningEvaluation
    {E C : SSet.{u}} [Quasicategory C] (p : E ⟶ C.op) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (y : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity y)) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p (SSet.opObjEquiv.symm y) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorEvaluate p
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity y))
      (canonicalYonedaUnstraighteningIdentity y) ≫
    eqToHom (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p) (canonicalYonedaUnstraighteningIdentity_projection y))

/-- 同じ全体からの恒等点評価は、任意の標的 left fibration に対して自明 Kan fibration。 -/
lemma canonicalYonedaUnstraighteningEvaluation_trivialKanFibration
    {E C : SSet.{u}} [Quasicategory C] (p : E ⟶ C.op) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (y : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (canonicalYonedaUnstraighteningEvaluation p y) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibrations.comp_mem _ _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorEvaluate_initial_trivialKanFibration p _ _
      (canonicalYonedaUnstraighteningIdentity_isInitialVertex y)).mem
    (MorphismProperty.rlp_of_isIso _ _)⟩

/-- 同じ全体の復元射から取る実際の評価も、全パラメーターで同値。 -/
lemma canonicalYonedaUnstraighteningEvaluation_isQCatEquivalence
    {E C : SSet.{u}} [Quasicategory C] (p : E ⟶ C.op) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (y : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (canonicalYonedaUnstraighteningEvaluation p y) := by
  have := canonicalYonedaUnstraighteningEvaluation_trivialKanFibration p y
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration _

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.CanonicalYonedaUnstraighteningIdentity
