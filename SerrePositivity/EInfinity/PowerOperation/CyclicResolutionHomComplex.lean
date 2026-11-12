module

public import SerrePositivity.EInfinity.PowerOperation.LinearHomComplexFunctor
public import SerrePositivity.EInfinity.PowerOperation.CyclicTensorInput

/-!
# 指定完全周期解像度からの Hom 複体

DAG XIII Construction 2.2.6 の鎖模型の前段。
整数全次数の同じ左正則解像度から、作用付き入力への Hom を取る。
全次数の積を持つ線形 Hom 複体そのものであり、非有界入力で native Tate と
同定できるという主張はここでは置かない。完全入力での比較と延長は別に行う。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory
open SerrePositivity.DifferentialGraded
variable (p : ℕ) [NeZero p] (k : Type u) [CommRing k]

/-- 周期の向きと次数を固定した、同じ左正則複体。 -/
def powerOperationCompleteResolution :
    CochainComplex (Rep.{u} k (PowerOperationCyclicGroup.{u} p)) ℤ :=
  cyclicTateComplex (Rep.leftRegular k (PowerOperationCyclicGroup.{u} p))
    (powerOperationCyclicGenerator p)

/-- 同じ完全周期解像度からの全 Hom 関手。 -/
def cyclicResolutionHomFunctor :
    CochainComplex (Rep.{u} k (PowerOperationCyclicGroup.{u} p)) ℤ ⥤
      CochainComplex (ModuleCat.{u} k) ℤ :=
  linearHomComplexFunctor k (powerOperationCompleteResolution p k)

/-- 元の符号付き p 入力に同じ解像度の Hom を適用する。 -/
def powerOperationTensorResolutionHom : Complex k ⥤ Complex k :=
  powerOperationTensorInput p k ⋙ cyclicResolutionHomFunctor p k

end SerrePositivity.EInfinity.PowerOperation
