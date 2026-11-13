module

public import SerrePositivity.EInfinity.PowerOperation.MayRepeatedZeroInput
public import SerrePositivity.EInfinity.PowerOperation.MayDValues
public import SerrePositivity.EInfinity.PowerOperation.MayZeroOperation

/-!
# May の零次作用と単位係数の作用の一致

May, Proposition 2.3(iii) の補助。同じ W→BE 比較の零次係数と同じ BE 作用を評価する。
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
open SerrePositivity.EInfinity.BarrattEccles
variable {k : Type u} [CommRing k] (X : (operad k).Algebra)

lemma mayCoefficientOperation_value (p : ℕ) (c : 𝟙_ (Complex k) ⟶ (operad k).arity p)
    (y : (power X.carrier p).X 0) :
    (coefficientOperation X p c).f 0 y =
      mayHomogeneousAction X p 0 0 (c.f 0 (mayTensorUnitValue (k := k))) y := by
  change (X.action p).f 0 ((cochainTensorMap c (𝟙 (power X.carrier p))).f 0
    ((λ_ (power X.carrier p)).inv.f 0 y)) = _
  rw [mayUnitLeftInverse_value, cochainTensorMap_apply_ι]
  rfl

lemma mayZeroCoefficientOperation_value (p : ℕ) [NeZero p]
    (y : (power X.carrier p).X 0) :
    (coefficientOperation X p (mayZeroCoefficient p k)).f 0 y =
      mayHomogeneousAction X p 0 0
        (mayActualCoefficient p 0 (mayCoefficientValue p k 0)) y := by
  rw [mayCoefficientOperation_value]
  have hc : (mayZeroCoefficient p k).f 0 (mayTensorUnitValue (k := k)) =
      mayActualCoefficient p 0 (mayCoefficientValue p k 0) := mayZeroCoefficient_value p k
  rw [hc]

lemma mayHomogeneousAction_zero_transport (p : ℕ) (j : ℤ) (hj : j = 0)
    (c : ((operad k).arity p).X 0) (y : (power X.carrier p).X j) :
    (eqToHom (congrArg (fun i : ℤ => X.carrier.X i) ((zero_add j).trans hj))).hom
      (mayHomogeneousAction X p 0 j c y) =
        mayHomogeneousAction X p 0 0 c
          ((eqToHom (congrArg (fun i : ℤ => (power X.carrier p).X i) hj)).hom y) := by
  subst j
  rfl

end SerrePositivity.EInfinity.PowerOperation
