module
public import SerrePositivity.KST.Fibration.ProductQuillenABaseChange
public import SerrePositivity.KST.SConstruction.RelativeFiberEquivalence

/-! # K-1 の相対 cofiber 左 fiber 定理の任意の厳密基底変換

同じ相対 fiber 内の ρ・θ による固定 K-1 入力を使い、K-2 の元の射対を結論する。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.KST.SConstruction
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration

/-- 相対 subobject 射の任意の厳密基底変換は、元の基底・quotient の積と局所化同値。 -/
theorem relativeCofiberBaseChange_localized_isIso {X : StableModel.{u}}
    (A B : ClosedStablePredicate X) {P T : SSet.{u}}
    {p : P ⟶ objectSConstructionFunctor.obj (relativeCofiberStableModel A B)}
    {q : P ⟶ T} {t : T ⟶ objectSConstructionFunctor.obj (closedStableModel A)}
    (h : IsPullback p q (objectSConstructionFunctor.map (relativeCofiberSubobject A B)) t) :
    IsIso (AnodyneHomotopy.anodyneQ.map
      (lift q (p ≫ objectSConstructionFunctor.map (relativeCofiberQuotient A B)))) := by
  apply productQuillenA_baseChange h
  intro m a
  exact relativeCofiberLeftFiberQuotient_localized_isIso A B a

end SerrePositivity.KST.Fibration
