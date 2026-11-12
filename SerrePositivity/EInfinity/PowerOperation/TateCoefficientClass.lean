module

public import SerrePositivity.EInfinity.PowerOperation.CyclicTensorInput
public import SerrePositivity.EInfinity.PowerOperation.CyclicTateTrivialHomology

/-!
# P⁰ の周期係数模型の指定類

DAG XIII Construction 2.2.6 の Tate 類に対応させる係数側の指定を固定する。
同じ巡回生成元と周期微分を用い、H^{-1} の 1 に対応する元を取る。
この係数模型と native な Tate スペクトル・双加群との比較は別の工程である。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory
variable (p : ℕ) [NeZero p] (k : Type u) [CommRing k] [CharP k p]

/-- 指定巡回生成元と自明係数による周期複体。 -/
def powerOperationTateCoefficientComplex : CochainComplex (ModuleCat.{u} k) ℤ :=
  (cyclicTateModuleComplexFunctor (powerOperationCyclicGenerator p)).obj
    (Rep.trivial k (PowerOperationCyclicGroup.{u} p) k)

/-- 同じ係数複体の全整数次数のホモロジーと k の指定同型。 -/
def powerOperationTateCoefficientHomologyIso (i : ℤ) :
    (powerOperationTateCoefficientComplex p k).homology i ≅ ModuleCat.of k k :=
  cyclicTateTrivialHomologyIso _ p (powerOperationCyclicGroup_card p)
    (powerOperationCyclicGenerator p) i

/-- 周期係数模型の H^{-1} における、1 に対応する指定類。 -/
def powerOperationTateCoefficientClass :
    (powerOperationTateCoefficientComplex p k).homology (-1) :=
  (powerOperationTateCoefficientHomologyIso p k (-1)).inv (1 : k)

lemma powerOperationTateCoefficientClass_value :
    (powerOperationTateCoefficientHomologyIso p k (-1)).hom
      (powerOperationTateCoefficientClass p k) = 1 := by
  simp [powerOperationTateCoefficientClass]

lemma powerOperationTateCoefficientClass_ne_zero [Nontrivial k] :
    powerOperationTateCoefficientClass p k ≠ 0 := by
  intro h
  have hv := powerOperationTateCoefficientClass_value p k
  rw [h, map_zero] at hv
  exact zero_ne_one hv

end SerrePositivity.EInfinity.PowerOperation
