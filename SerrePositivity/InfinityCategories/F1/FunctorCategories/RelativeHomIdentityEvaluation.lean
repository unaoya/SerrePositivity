module

public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeHomCosliceEquivalence
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorOverEquivalence

/-!
概要：Hom 関手の unstraightening を始域とする相対関手を、実際の恒等点で評価する。
方針：同じ大域 coslice 同値で前合成し、恒等錐での自明 Kan 評価と比較する。
規約：標的は任意の同じ底上の left fibration。恒等点での実際の評価そのものを使う。
使われ方：任意の coherent 変換の恒等射での回収の同値性へ接続する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 元の Hom unstraightening の実際の恒等点で、任意の相対関手を評価する。 -/
def relativeHomIdentityEvaluate {B : SSet.{u}} (q : LeftFibrationObject B)
    {E : SSet.{u + 1}} (p : E ⟶ LeftFibrationInfinity B) :
    relativeFunctorSpace p
      (leftUnstraighteningProjection (leftFibrationCoherentEvaluation q.val)) ⟶
        vertexFiber p (coherentNerveVertex q) :=
  relativeFunctorEvaluate p
    (leftUnstraighteningProjection (leftFibrationCoherentEvaluation q.val))
    (relativeHomUnstraighteningIdentity q).val ≫
    eqToHom (congrArg (vertexFiber p) (relativeHomUnstraighteningIdentity_projection q))

/-- 正規化した恒等点評価の包含後は、元の全空間での同じ頂点評価。 -/
lemma relativeHomIdentityEvaluate_ι {B : SSet.{u}} (q : LeftFibrationObject B)
    {E : SSet.{u + 1}} (p : E ⟶ LeftFibrationInfinity B) :
    relativeHomIdentityEvaluate q p ≫ vertexFiberι p (coherentNerveVertex q) =
      vertexFiberι ((ihom (leftUnstraightening (leftFibrationCoherentEvaluation q.val))).map p)
        (functorVertex (leftUnstraighteningProjection (leftFibrationCoherentEvaluation q.val))) ≫
        evaluateFunctorAt (relativeHomUnstraighteningIdentity q).val := by
  dsimp only [relativeHomIdentityEvaluate]
  rw [Category.assoc, vertexFiberTransport_ι p (relativeHomUnstraighteningIdentity_projection q)]
  exact relativeFunctorEvaluate_ι p _ (relativeHomUnstraighteningIdentity q).val

/-- 同じ大域比較で前合成した後の恒等錐評価は、元の恒等点評価に厳密に一致。 -/
lemma relativeHomIdentityEvaluate_precomp {B : SSet.{u}} (q : LeftFibrationObject B)
    {E : SSet.{u + 1}} (p : E ⟶ LeftFibrationInfinity B) :
    relativeFunctorOverPre p
      (Over.homMk (U := Over.mk (sliceUnderProjection
        (SSet.yonedaEquiv.symm (coherentNerveVertex q))))
        (V := Over.mk (leftUnstraighteningProjection (leftFibrationCoherentEvaluation q.val)))
        (relativeHomCosliceComparison q) (relativeHomCosliceComparison_projection q)) ≫
      leftFibrationCoslicePointEvaluate p (coherentNerveVertex q) =
      relativeHomIdentityEvaluate q p := by
  apply (cancel_mono (vertexFiberι p (coherentNerveVertex q))).1
  rw [Category.assoc, leftFibrationCoslicePointEvaluate_ι, relativeHomIdentityEvaluate_ι]
  change (vertexFiberι _ _ ≫ (pre (relativeHomCosliceComparison q)).app E) ≫
    evaluateFunctorAt (cosliceIdentityCone (coherentNerveVertex q)) = _
  rw [Category.assoc, evaluateFunctorAt_pre, relativeHomCosliceComparison_identity]
  rfl

/-- 恒等点での元の評価は、任意の同じ底上の left fibration に対して同値。 -/
lemma relativeHomIdentityEvaluate_isQCatEquivalence {B : SSet.{u}}
    (q : LeftFibrationObject B) {E : SSet.{u + 1}}
    (p : E ⟶ LeftFibrationInfinity B) [LeftFibration p] :
    IsQCatEquivalence (relativeHomIdentityEvaluate q p) := by
  have : KanComplex (vertexFiber p (coherentNerveVertex q)) :=
    vertexFiber_kanComplex_of_leftFibration p _
  have he := relativeFunctorOverPre_isQCatEquivalence p
    (Over.homMk (U := Over.mk (sliceUnderProjection
      (SSet.yonedaEquiv.symm (coherentNerveVertex q))))
      (V := Over.mk (leftUnstraighteningProjection (leftFibrationCoherentEvaluation q.val)))
      (relativeHomCosliceComparison q) (relativeHomCosliceComparison_projection q))
    (relativeHomCosliceComparison_isQCatEquivalence q).isPrecompositionEquivalence
  have ht := leftFibrationCoslicePointEvaluate_trivialKanFibration p (coherentNerveVertex q)
  have h := he.comp (isQCatEquivalence_of_trivialKanFibration
    (leftFibrationCoslicePointEvaluate p (coherentNerveVertex q)))
  rw [relativeHomIdentityEvaluate_precomp] at h
  exact h

end SerrePositivity.InfinityCategories
