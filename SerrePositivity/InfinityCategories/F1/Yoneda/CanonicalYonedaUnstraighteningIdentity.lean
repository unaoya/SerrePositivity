module

public import SerrePositivity.InfinityCategories.F1.TwistedArrow.TargetReconstruction
public import SerrePositivity.InfinityCategories.F1.Yoneda.RightRepresentableTwistedArrowEquivalence
public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftFibrationInitialEvaluation
public import SerrePositivity.InfinityCategories.Stable.ColimitCoconeFamily

/-!
概要：Tw 全体の同じ復元射から、実際の Yoneda 前層の恒等点と評価を取る。
方針：元の反転 coslice の恒等点を、終点固定に制限した全体の復元射で送る。
規約：以前の別々に選んだ比較の評価点との一致は仮定しない。
使われ方：同じ全体の射の自然性を使い、c1 の fiber 輸送を twisted arrow の輸送へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

attribute [local instance] vertexFiber_kanComplex_of_leftFibration

local instance {C : SSet.{u}} [Quasicategory C] : Quasicategory (C.op ⊗ C) :=
  quasicategory_of_innerFibration (fst C.op C)

local instance {C : SSet.{u}} [Quasicategory C] (y : C _⦋0⦌) :
    Quasicategory (smallLeftUnstraightening (representablePresheafInfinity y)) :=
  quasicategory_of_innerFibration
    (smallLeftUnstraighteningProjection (representablePresheafInfinity y))

/-- 元の反転 coslice から終点固定の twisted arrow への比較も前合成同値。 -/
lemma cosliceToTwistedArrowTarget_isPrecompositionEquivalence
    {C : SSet.{u}} [Quasicategory C] (y : C _⦋0⦌) :
    IsPrecompositionEquivalence (cosliceToTwistedArrowTarget y) := by
  have h := rightRepresentableTwistedArrowMap_isPrecompositionEquivalence y
  change IsPrecompositionEquivalence
    ((cofinalPointSliceOverOpIso y).hom.left ≫ cosliceToTwistedArrowTarget y) at h
  exact (isPrecompositionEquivalence_of_iso
    ((Over.forget C.op).mapIso (cofinalPointSliceOverOpIso y))).cancel_left h

/-- 全体の同じ復元射から取る、元の反転 coslice との比較。 -/
def canonicalYonedaCosliceComparison {C : SSet.{u}} [Quasicategory C] (y : C _⦋0⦌) :
    sliceUnder (SSet.yonedaEquiv.symm (SSet.opObjEquiv.symm y)) ⟶
      smallLeftUnstraightening (representablePresheafInfinity y) :=
  cosliceToTwistedArrowTarget y ≫ twistedArrowTargetReconstruction y

/-- 同じ比較は元の反転した底を厳密に保つ。 -/
lemma canonicalYonedaCosliceComparison_projection
    {C : SSet.{u}} [Quasicategory C] (y : C _⦋0⦌) :
    canonicalYonedaCosliceComparison y ≫
      smallLeftUnstraighteningProjection (representablePresheafInfinity y) =
    sliceUnderProjection (SSet.yonedaEquiv.symm (SSet.opObjEquiv.symm y)) := by
  rw [canonicalYonedaCosliceComparison, Category.assoc,
    twistedArrowTargetReconstruction_projection, cosliceToTwistedArrowTarget_projection]

/-- 同じ比較を全体へ戻すと、元の錐の比較と全体の復元射の合成そのもの。 -/
lemma canonicalYonedaCosliceComparison_global
    {C : SSet.{u}} [Quasicategory C] (y : C _⦋0⦌) :
    canonicalYonedaCosliceComparison y ≫
      smallLeftUnstraighteningMap (representablePresheafInfinity y) (twistedArrowHomInfinity C)
        (twistedArrowTargetInclusion y)
        (representablePresheafInfinity_eq_targetRestriction y).symm =
    cosliceOppositeTwistedArrowMap (SSet.yonedaEquiv.symm (SSet.opObjEquiv.symm y)) ≫
      leftStraighteningInfinityReconstruction (twistedArrowProjection C) := by
  rw [canonicalYonedaCosliceComparison, Category.assoc, twistedArrowTargetReconstruction_map,
    ← Category.assoc, cosliceToTwistedArrowTarget, pullback.lift_fst]

/-- 同じ coslice 比較は全空間で前合成同値。 -/
lemma canonicalYonedaCosliceComparison_isPrecompositionEquivalence
    {C : SSet.{u}} [Quasicategory C] (y : C _⦋0⦌) :
    IsPrecompositionEquivalence (canonicalYonedaCosliceComparison y) :=
  (cosliceToTwistedArrowTarget_isPrecompositionEquivalence y).comp
    (twistedArrowTargetReconstruction_isPrecompositionEquivalence y)

/-- Tw 全体の同じ復元射を終点固定で読む、実際の Yoneda 前層内の恒等点。 -/
def canonicalYonedaUnstraighteningIdentity
    {C : SSet.{u}} [Quasicategory C] (y : C _⦋0⦌) :
    (smallLeftUnstraightening (representablePresheafInfinity y)) _⦋0⦌ :=
  (canonicalYonedaCosliceComparison y).app (Opposite.op ⦋0⦌)
    (cosliceIdentityCone (SSet.opObjEquiv.symm y))

/-- 恒等点の全体での像も、同じ Tw の恒等錐を元の復元射で送った点。 -/
lemma canonicalYonedaUnstraighteningIdentity_global
    {C : SSet.{u}} [Quasicategory C] (y : C _⦋0⦌) :
    (smallLeftUnstraighteningMap (representablePresheafInfinity y) (twistedArrowHomInfinity C)
      (twistedArrowTargetInclusion y)
      (representablePresheafInfinity_eq_targetRestriction y).symm).app
        (Opposite.op ⦋0⦌) (canonicalYonedaUnstraighteningIdentity y) =
    (leftStraighteningInfinityReconstruction (twistedArrowProjection C)).app (Opposite.op ⦋0⦌)
      ((cosliceOppositeTwistedArrowMap
        (SSet.yonedaEquiv.symm (SSet.opObjEquiv.symm y))).app (Opposite.op ⦋0⦌)
        (cosliceIdentityCone (SSet.opObjEquiv.symm y))) :=
  congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌)
    (cosliceIdentityCone (SSet.opObjEquiv.symm y))) (canonicalYonedaCosliceComparison_global y)

/-- 同じ恒等点の射影は、指定した元の頂点である。 -/
lemma canonicalYonedaUnstraighteningIdentity_projection
    {C : SSet.{u}} [Quasicategory C] (y : C _⦋0⦌) :
    (smallLeftUnstraighteningProjection (representablePresheafInfinity y)).app
      (Opposite.op ⦋0⦌) (canonicalYonedaUnstraighteningIdentity y) = SSet.opObjEquiv.symm y := by
  have h := congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌)
    (cosliceIdentityCone (SSet.opObjEquiv.symm y)))
    (canonicalYonedaCosliceComparison_projection y)
  exact h.trans (cosliceIdentityCone_projection _)

/-- 全体から取った同じ恒等点は、実際の unstraightening 全空間の始対象。 -/
lemma canonicalYonedaUnstraighteningIdentity_isInitialVertex
    {C : SSet.{u}} [Quasicategory C] (y : C _⦋0⦌) :
    IsInitialVertex (canonicalYonedaUnstraighteningIdentity y) := by
  have h := canonicalYonedaCosliceComparison_isPrecompositionEquivalence y
  exact h.isQCatEquivalence.choose.map_isInitialVertex (cosliceIdentityCone_isInitialVertex _)

/-- 全体から取った同じ恒等点で、元の全相対 Hom を直接評価する。 -/
def canonicalYonedaUnstraighteningEvaluation
    {E C : SSet.{u}} [Quasicategory C] (p : E ⟶ C.op) [LeftFibration p] (y : C _⦋0⦌) :
    relativeFunctorSpace p
      (smallLeftUnstraighteningProjection (representablePresheafInfinity y)) ⟶
      vertexFiber p (SSet.opObjEquiv.symm y) :=
  relativeFunctorEvaluate p
      (smallLeftUnstraighteningProjection (representablePresheafInfinity y))
      (canonicalYonedaUnstraighteningIdentity y) ≫
    eqToHom (congrArg (vertexFiber p) (canonicalYonedaUnstraighteningIdentity_projection y))

/-- 同じ全体からの恒等点評価は、任意の標的 left fibration に対して自明 Kan fibration。 -/
lemma canonicalYonedaUnstraighteningEvaluation_trivialKanFibration
    {E C : SSet.{u}} [Quasicategory C] (p : E ⟶ C.op) [LeftFibration p] (y : C _⦋0⦌) :
    TrivialKanFibration (canonicalYonedaUnstraighteningEvaluation p y) :=
  ⟨trivialKanFibrations.comp_mem _ _
    (relativeFunctorEvaluate_initial_trivialKanFibration p _ _
      (canonicalYonedaUnstraighteningIdentity_isInitialVertex y)).mem
    (MorphismProperty.rlp_of_isIso _ _)⟩

/-- 同じ全体の復元射から取る実際の評価も、全パラメーターで同値。 -/
lemma canonicalYonedaUnstraighteningEvaluation_isQCatEquivalence
    {E C : SSet.{u}} [Quasicategory C] (p : E ⟶ C.op) [LeftFibration p] (y : C _⦋0⦌) :
    IsQCatEquivalence (canonicalYonedaUnstraighteningEvaluation p y) := by
  have := canonicalYonedaUnstraighteningEvaluation_trivialKanFibration p y
  exact isQCatEquivalence_of_trivialKanFibration _

end SerrePositivity.InfinityCategories
