module

public import SerrePositivity.InfinityCategories.F1.Yoneda.RepresentableUnstraighteningComparison
public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftFibrationInitialEvaluation

/-!
概要：実際の Yoneda 前層の左 unstraightening からの相対射を恒等点で評価する。
方針：元の表現可能 coslice への制限の同値と、始対象での評価の自明 Kan 性を合成する。
規約：任意の標的 left fibration と全高次パラメーターを扱う。
使われ方：同じ表現可能前層から任意の前層への変換の Yoneda 評価。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 元の coslice から同じ Yoneda 前層の左 unstraightening への底上の比較。 -/
def representableCosliceUnstraighteningComparison
    {C : SSet.{u}} [Quasicategory C] (y : C _⦋0⦌) :
    sliceUnder (SSet.yonedaEquiv.symm (SSet.opObjEquiv.symm y)) ⟶
      smallLeftUnstraightening (representablePresheafInfinity y) :=
  (cofinalPointSliceOverOpIso y).inv.left ≫ representableLeftUnstraighteningComparison y

/-- 同じ coslice 比較は、元の反転した底を厳密に保つ。 -/
lemma representableCosliceUnstraighteningComparison_projection
    {C : SSet.{u}} [Quasicategory C] (y : C _⦋0⦌) :
    representableCosliceUnstraighteningComparison y ≫
      smallLeftUnstraighteningProjection (representablePresheafInfinity y) =
    sliceUnderProjection (SSet.yonedaEquiv.symm (SSet.opObjEquiv.symm y)) := by
  rw [representableCosliceUnstraighteningComparison, Category.assoc,
    representableLeftUnstraighteningComparison_projection]
  exact (cofinalPointSliceOverOpIso y).inv.w

/-- 同じ coslice 比較は全空間の前合成同値。 -/
lemma representableCosliceUnstraighteningComparison_isPrecompositionEquivalence
    {C : SSet.{u}} [Quasicategory C] (y : C _⦋0⦌) :
    IsPrecompositionEquivalence (representableCosliceUnstraighteningComparison y) :=
  (isPrecompositionEquivalence_of_iso
    ((Over.forget C.op).mapIso (cofinalPointSliceOverOpIso y).symm)).comp
      (representableLeftUnstraighteningComparison_isPrecompositionEquivalence y)

/-- 同じ Yoneda 前層の左 unstraightening からの相対射を、元の恒等錐で評価する。 -/
def representableUnstraighteningEvaluation
    {E C : SSet.{u}} [Quasicategory C] (p : E ⟶ C.op) [LeftFibration p]
    (y : C _⦋0⦌) :
    relativeFunctorSpace p
      (smallLeftUnstraighteningProjection (representablePresheafInfinity y)) ⟶
        vertexFiber p (SSet.opObjEquiv.symm y) :=
  relativeFunctorOverPre p
      (Over.homMk
        (U := Over.mk (sliceUnderProjection
          (SSet.yonedaEquiv.symm (SSet.opObjEquiv.symm y))))
        (V := Over.mk (smallLeftUnstraighteningProjection (representablePresheafInfinity y)))
        (representableCosliceUnstraighteningComparison y)
        (representableCosliceUnstraighteningComparison_projection y)) ≫
    relativeFunctorEvaluate p
      (sliceUnderProjection (SSet.yonedaEquiv.symm (SSet.opObjEquiv.symm y)))
      (cosliceIdentityCone (SSet.opObjEquiv.symm y)) ≫
    eqToHom (congrArg (vertexFiber p)
      (cosliceIdentityCone_projection (SSet.opObjEquiv.symm y)))

/-- この実際の評価射は、任意の標的 left fibration に対して同値。 -/
lemma representableUnstraighteningEvaluation_isQCatEquivalence
    {E C : SSet.{u}} [Quasicategory C] (p : E ⟶ C.op) [LeftFibration p]
    (y : C _⦋0⦌) : IsQCatEquivalence (representableUnstraighteningEvaluation p y) := by
  have h₁ := relativeFunctorOverPre_isQCatEquivalence p
    (Over.homMk
        (U := Over.mk (sliceUnderProjection
          (SSet.yonedaEquiv.symm (SSet.opObjEquiv.symm y))))
        (V := Over.mk (smallLeftUnstraighteningProjection (representablePresheafInfinity y)))
        (representableCosliceUnstraighteningComparison y)
      (representableCosliceUnstraighteningComparison_projection y))
    (representableCosliceUnstraighteningComparison_isPrecompositionEquivalence y)
  have := leftFibration_cosliceIdentityEvaluation_trivialKanFibration p
    (SSet.opObjEquiv.symm y)
  have h₂ := isQCatEquivalence_of_trivialKanFibration
    (relativeFunctorEvaluate p
      (sliceUnderProjection (SSet.yonedaEquiv.symm (SSet.opObjEquiv.symm y)))
      (cosliceIdentityCone (SSet.opObjEquiv.symm y)))
  exact h₁.comp (h₂.comp (qCatEquivalenceOfIso
    (eqToIso (congrArg (vertexFiber p)
      (cosliceIdentityCone_projection (SSet.opObjEquiv.symm y))))).isQCatEquivalence)

end SerrePositivity.InfinityCategories
