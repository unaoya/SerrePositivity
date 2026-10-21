module

public import SerrePositivity.InfinityCategories.HomotopyLimits.RelativeEvaluationTransport
public import SerrePositivity.InfinityCategories.HomotopyLimits.YonedaRelativeCompositionEvaluation

/-!
概要：元の Yoneda 恒等点評価の底方向の自然性。
方針：元の表現可能 unstraightening の恒等点を全相対評価の輸送比較へ代入する。
規約：同じ恒等点と全相対 Hom を保持し、点ごとの比較の自然性を仮定しない。
使われ方：元の有限余積の脚の両側を、同じ評価点の輸送へ比較する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 元の恒等点を先に輸送した全評価は、元の恒等点評価後の輸送と全族で同型。 -/
def canonicalYonedaRelativeEvaluation_transportIso
    {E C : SSet.{u}} [Quasicategory C] (p : E ⟶ C.op) [LeftFibration p]
    (x y : C _⦋0⦌) (e : SSet.Edge (SSet.opObjEquiv.symm y) (SSet.opObjEquiv.symm x)) :
    FunctorIso
      (lift (SSet.const (canonicalYonedaIdentityFiber y))
          (𝟙 (relativeFunctorSpace p
            (smallLeftUnstraighteningProjection (representablePresheafInfinity y)))) ≫
        (edgeTransport
            (smallLeftUnstraighteningProjection (representablePresheafInfinity y)) e ▷
          relativeFunctorSpace p
            (smallLeftUnstraighteningProjection (representablePresheafInfinity y))) ≫
        relativeFunctorFiberEvaluation
          (smallLeftUnstraighteningProjection (representablePresheafInfinity y)) p
          (SSet.opObjEquiv.symm x))
      (canonicalYonedaUnstraighteningEvaluation p y ≫ edgeTransport p e) := by
  let q := smallLeftUnstraighteningProjection (representablePresheafInfinity y)
  let j := lift (SSet.const (canonicalYonedaIdentityFiber y)) (𝟙 (relativeFunctorSpace p q))
  have he : j ≫ relativeFunctorFiberEvaluation q p (SSet.opObjEquiv.symm y) =
      canonicalYonedaUnstraighteningEvaluation p y := by
    rw [canonicalYonedaUnstraighteningEvaluation_eq_fiberEvaluation]
    exact relativeFunctorFiberEvaluation_point q p _ (canonicalYonedaIdentityFiber y)
  have h := (relativeFunctorEvaluation_transportIso q p e).precomp j
  simpa only [← Category.assoc, he] using h

end SerrePositivity.InfinityCategories.HomotopyLimits
