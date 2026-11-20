module

public import SerrePositivity.AlgebraicGeometry.ProductCenter
public import SerrePositivity.AlgebraicGeometry.IdealFlattening
public import Mathlib.RingTheory.Finiteness.Ideal

/-!
概要：KST §5、Stacks 0810, Lemma 38.30.2 の境界元倍の係数中心と実チャート。
方針：積イデアルを中心とし、正則な拡大中心から係数イデアルの正則単項化を導く。
規約：この単項化には境界元の元の環での正則性は仮定しない。
使われ方：有限型加群の平坦化で係数イデアルの blowup 中心を実際に選ぶ。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry

variable {R : Type*} [CommRing R] (f : R) (I : Ideal R)

/--
概要：境界元と係数イデアルの積で定める中心。
方針：境界の単項イデアルと係数イデアルの積を取る。
規約：KST §5、Stacks 0810, Lemma 38.30.2。
使われ方：境界外を変えずに係数イデアルを単項化する。
-/
def boundaryMultipleCenter : Ideal R := Ideal.span {f} * I

/--
概要：有限生成な係数イデアルの境界元倍の中心は有限生成。
方針：単項イデアルと有限生成イデアルの積の有限生成性を使う。
規約：KST §5、Stacks 0810, Lemma 38.30.2、Noether 性は不要。
使われ方：実際の blowup の有限生成中心。
-/
theorem boundaryMultipleCenter_fg (hI : I.FG) : (boundaryMultipleCenter f I).FG :=
  (Submodule.fg_span_singleton f).mul hI

/--
概要：係数イデアルに境界の冪が入れば、境界元倍の中心に一つ大きい冪が入る。
方針：二つのイデアルの元の積の所属を使う。
規約：KST §5、Stacks 0810, Lemma 38.30.2、指数零も許す。
使われ方：中心の境界外での単位性。
-/
theorem pow_mem_boundaryMultipleCenter (n : ℕ) (hn : f ^ n ∈ I) :
    f ^ (n + 1) ∈ boundaryMultipleCenter f I := by
  rw [pow_succ']
  exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self f) hn

/--
概要：係数イデアルが境界の冪を含めば、境界元倍の中心補開集合は D(f) に等しい。
方針：中心が (f) に含まれることと、中心に境界の冪が入ることを双方向に使う。
規約：KST §5、Stacks 0810, Lemma 38.30.2、境界の正則性は不要。
使われ方：admissible な中心の補開集合を正確に指定する。
-/
theorem boundaryMultipleCenter_complement (n : ℕ) (hn : f ^ n ∈ I) :
    affineCenterComplement (boundaryMultipleCenter f I) = PrimeSpectrum.basicOpen f := by
  apply le_antisymm
  · intro x hx hf
    apply (mem_affineCenterComplement _ x).mp hx
    exact le_trans Ideal.mul_le_left (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hf))
  · exact basicOpen_le_affineCenterComplement_of_pow_mem _ f (n + 1)
      (pow_mem_boundaryMultipleCenter f I n hn)

/--
概要：境界元倍の中心の任意の実チャートで、係数イデアルの拡大は実際の正則単項イデアル。
方針：拡大中心を正則なチャート中心元で生成し、境界元倍のイデアルから正則因子を取り出す。
規約：KST §5、Stacks 0810, Lemma 38.30.2、空チャートも含む。
使われ方：係数イデアルの基底変更公式と合わせて小行列式の可除性を得る。
-/
theorem boundaryMultipleCenter_chart_regular_principal (a : boundaryMultipleCenter f I) :
    ∃ c : BlowupChartRing (boundaryMultipleCenter f I) a,
      c ∈ nonZeroDivisors _ ∧
      I.map (chartBaseMap (boundaryMultipleCenter f I) a) = Ideal.span {c} ∧
      chartBaseMap (boundaryMultipleCenter f I) a f * c =
        chartBaseMap (boundaryMultipleCenter f I) a a.val := by
  let φ := chartBaseMap (boundaryMultipleCenter f I) a
  have hprod : Ideal.span {φ f} * I.map φ =
      Ideal.span {φ a.val} := by
    have hspan : (Ideal.span {f}).map φ = Ideal.span {φ f} := by
      rw [Ideal.map_span, Set.image_singleton]
    rw [← hspan, ← Ideal.map_mul]
    exact chart_map_ideal_eq_span _ a
  exact ideal_regular_principal_of_regular_multiple (I.map φ) (φ f) (φ a.val)
    (chartBaseMap_mem_nonZeroDivisors _ a) hprod

/--
概要：係数イデアルが境界冪を含めば、チャート上の正則な共通因子は同じ境界冪を割る。
方針：冪の所属をチャートへ送り、正則単項の生成元による所属判定を使う。
規約：KST §5、Stacks 0810, Lemma 38.30.2、共通因子と境界元を区別する。
使われ方：共通因子の純変換から元の境界の純変換への比較全射を作る。
-/
theorem boundaryMultipleCenter_chart_regular_principal_dvd_pow
    (n : ℕ) (hn : f ^ n ∈ I) (a : boundaryMultipleCenter f I) :
    ∃ c : BlowupChartRing (boundaryMultipleCenter f I) a,
      c ∈ nonZeroDivisors _ ∧
      I.map (chartBaseMap (boundaryMultipleCenter f I) a) = Ideal.span {c} ∧
      c ∣ chartBaseMap (boundaryMultipleCenter f I) a f ^ n := by
  obtain ⟨c, hc, hC, _⟩ := boundaryMultipleCenter_chart_regular_principal f I a
  refine ⟨c, hc, hC, ?_⟩
  have h := Ideal.mem_map_of_mem (chartBaseMap (boundaryMultipleCenter f I) a) hn
  rw [hC, map_pow] at h
  exact Ideal.mem_span_singleton.mp h

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
