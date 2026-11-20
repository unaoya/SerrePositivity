module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.ChartEmbedding

/-!
概要：KST §5、Stacks 0815 の Cartier 境界元は通常 blowup のチャートでも正則。
方針：基礎環の局所化へのチャートの単射を使って正則性を反映する。
規約：境界元とチャートを指定する中心元は異なってよい。
使われ方：イデアル加群の純変換と拡大イデアルの比較。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry

variable {R : Type*} [CommRing R] (I : Ideal R) (a : I)

/--
概要：基礎環の非零因子は標準 blowup チャートでも非零因子。
方針：局所化での非零因子性とチャートの局所化への単射を使う。
規約：KST §5、Stacks 0815、中心元 a 自身の基礎環での正則性は不要。
使われ方：境界元の正則作用による純変換の像の同定。
-/
theorem chartBaseMap_nonZeroDivisors {f : R} (hf : f ∈ nonZeroDivisors R) :
    chartBaseMap I a f ∈ nonZeroDivisors (BlowupChartRing I a) := by
  have hloc : algebraMap R (Localization.Away a.1) f ∈
      nonZeroDivisors (Localization.Away a.1) :=
    IsLocalization.nonZeroDivisors_le_comap (S := Localization.Away a.1) (Submonoid.powers a.1) hf
  apply mem_nonZeroDivisors_iff_left.mpr
  intro z hz
  apply chartToBaseLocalization_injective I a
  rw [map_zero]
  apply (mem_nonZeroDivisors_iff_left.mp hloc)
  simpa only [map_mul, chartToBaseLocalization_base, map_zero] using
    congrArg (chartToBaseLocalization I a) hz

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
