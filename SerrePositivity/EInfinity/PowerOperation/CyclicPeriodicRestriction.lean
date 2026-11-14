module

public import SerrePositivity.EInfinity.PowerOperation.CyclicResolutionHomComplex
public import SerrePositivity.EInfinity.PowerOperation.LinearHomComplexPrecomposition
public import SerrePositivity.HomologicalAlgebra.Complex.Truncation
public import Mathlib.Data.Int.Interval

/-!
# 同じ完全周期解像度の正の部分への全自然な制限

DAG XIII Construction 2.2.6 の Tate 境界の鎖模型に用いる前段。
完全周期解像度の非負次数の部分への前合成を取り、値域が上有界なら
各次数で残る成分が有限区間に収まることを証明する。
この時点で、実 homotopy orbit との比較を済ませたとは主張しない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory CochainComplex HomComplex
variable (p : ℕ) [NeZero p] (k : Type u) [CommRing k]

/-- 同じ完全周期解像度の非負次数の部分。 -/
def cyclicPositiveResolution := StupidTruncation.above (powerOperationCompleteResolution p k) 0

/-- 正の部分からの同じ全 Hom 関手。 -/
def cyclicPositiveResolutionHomFunctor :
    CochainComplex (Rep.{u} k (PowerOperationCyclicGroup.{u} p)) ℤ ⥤
      CochainComplex (ModuleCat.{u} k) ℤ :=
  linearHomComplexFunctor k (cyclicPositiveResolution p k)

/-- 同じ周期解像度の包含による、全係数に自然な制限射。 -/
def cyclicPeriodicRestriction : cyclicResolutionHomFunctor p k ⟶
    cyclicPositiveResolutionHomFunctor p k :=
  linearHomComplexPrecomposition k
    (StupidTruncation.inclusion (powerOperationCompleteResolution p k) 0)

/-- 上有界な係数では、同じ Hom の各次数の成分は有限区間に収まる。 -/
lemma cyclicPositiveResolutionHom_finiteSupport
    (M : CochainComplex (Rep.{u} k (PowerOperationCyclicGroup.{u} p)) ℤ)
    (d : ℤ) [M.IsStrictlyLE d] (n : ℤ)
    (z : Cochain (cyclicPositiveResolution p k) M n)
    (i j : ℤ) (hij : i + n = j) (hi : i ∉ Finset.Icc 0 (d - n)) : z.v i j hij = 0 := by
  by_cases h : i < 0
  · exact (StupidTruncation.above_isZero_X
      (powerOperationCompleteResolution p k) 0 i h).eq_of_src _ _
  · have hj : d < j := by
      have hle : 0 ≤ i := by omega
      have hnot : ¬i ≤ d - n := by
        intro hin
        exact hi (Finset.mem_Icc.mpr ⟨hle, hin⟩)
      omega
    exact (M.isZero_of_isStrictlyLE d j hj).eq_of_tgt _ _

end SerrePositivity.EInfinity.PowerOperation
