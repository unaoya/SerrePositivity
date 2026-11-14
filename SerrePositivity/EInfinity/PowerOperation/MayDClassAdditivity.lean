module

public import SerrePositivity.EInfinity.PowerOperation.MayCoefficientNormTransfer
public import SerrePositivity.EInfinity.PowerOperation.MayNormCoefficient
public import SerrePositivity.EInfinity.PowerOperation.MayClosedTensor
public import SerrePositivity.EInfinity.PowerOperation.MayDClasses
public import Mathlib.Tactic.Abel

/-!
# May の指定 D_i の加法性

May, Proposition 2.3(ii)。同じ混合差のノルム表示と指定された境界係数を使う。
ノルム係数は実境界であり、閉入力とのテンソルの類が零になることから加法性を得る。
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
open SerrePositivity.EInfinity.BarrattEccles
variable (p : ℕ) [Fact p.Prime] (X : (operad (ZMod p)).Algebra)

/-- 全指定 D_s の実ホモロジー類は、閉入力の和について加法的。 -/
lemma mayDClass_add (s : ℕ) (q : ℤ) (a b : MayClosed X.carrier q) :
    mayDClass p X s q (a + b) = mayDClass p X s q a + mayDClass p X s q b := by
  let c := mayNormCoefficientClosed p s
  let y : MayClosed (power X.carrier p) (mayRepeatedDegree q p) :=
    ⟨mayMixedInputRepresentative p X.carrier q a.val b.val,
      mayMixedInputRepresentative_cycle p X.carrier q a.val b.val a.property b.property⟩
  let t := mayClosedTensor (-(s : ℤ)) (mayRepeatedDegree q p) c y
  let z := mayClosedMap (X.action p) (-(s : ℤ) + mayRepeatedDegree q p) t
  have hv : mayDClosed X p s q (a + b) - mayDClosed X p s q a - mayDClosed X p s q b = z := by
    apply Subtype.ext
    change mayDValue X p s q (a.val + b.val) - mayDValue X p s q a.val - mayDValue X p s q b.val =
      mayHomogeneousAction X p (-(s : ℤ)) (mayRepeatedDegree q p) c.val y.val
    dsimp only [c, y]
    rw [mayNormCoefficientClosed_value, mayCoefficientNorm_transfer,
      mayMixedInputRepresentative_norm]
    change _ = (mayHomogeneousActionLinear X p (-(s : ℤ)) (mayRepeatedDegree q p)
      (mayActualCoefficient p s (mayCoefficientValue p (ZMod p) s)))
        (mayRepeatedValue X.carrier q (a.val + b.val) p -
          mayRepeatedValue X.carrier q a.val p - mayRepeatedValue X.carrier q b.val p)
    rw [map_sub, map_sub]
    rfl
  have ht : mayClosedClass _ _ t = 0 := mayClosedTensor_class_zero_left
    (-(s : ℤ)) (mayRepeatedDegree q p) c y (mayNormCoefficientClosed_class p s)
  have hn := mayClosedClass_naturality (X.action p) (-(s : ℤ) + mayRepeatedDegree q p) t
  change (homologyMap (X.action p) (-(s : ℤ) + mayRepeatedDegree q p)).hom
    (mayClosedClass (cochainTensor ((operad (ZMod p)).arity p) (power X.carrier p))
      (-(s : ℤ) + mayRepeatedDegree q p) t) = mayClosedClass X.carrier _ z at hn
  rw [ht] at hn
  have hz : mayClosedClass X.carrier (-(s : ℤ) + mayRepeatedDegree q p) z = 0 :=
    hn.symm.trans (map_zero (homologyMap (X.action p) _).hom)
  rw [← hv, map_sub, map_sub] at hz
  apply sub_eq_zero.mp
  calc
    mayDClass p X s q (a + b) - (mayDClass p X s q a + mayDClass p X s q b) =
      mayDClass p X s q (a + b) - mayDClass p X s q a - mayDClass p X s q b := by abel
    _ = 0 := hz

end SerrePositivity.EInfinity.PowerOperation
