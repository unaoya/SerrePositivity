module

public import SerrePositivity.AlgebraicGeometry.ChartEmbedding

/-!
概要：KST §5 の blowup の普遍性のための標準チャートの正則な持ち上げ。
方針：中心の像が正則な一元で生成されるとき、斉次分数の像を局所化の中から標的環へ戻す。
規約：実際の環準同型を構成し、存在する射を仮定しない。
使われ方：admissible blowup の共通細分と合成の支配。
-/

@[expose] public noncomputable section

universe u v
namespace SerrePositivity.AlgebraicGeometry
open Polynomial
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
  (I : Ideal R) (f : R →+* S) (a : I)

/--
概要：標準チャートの斉次分数を標的環の f(a) 局所化に送る写像。
方針：基底環の a 局所化へのチャート埋め込みと係数の局所化写像を合成する。
規約：KST §5、標的環への持ち上げの前に通常の局所化で計算する。
使われ方：正則な単項中心へのチャート持ち上げ。
-/
def chartToLocalizedTarget : BlowupChartRing I a →+* Localization.Away (f a.1) :=
  (Localization.awayMap f a.1).comp (chartToBaseLocalization I a)

/--
概要：標的局所化へのチャート写像は基底係数を保存する。
方針：二つの局所化写像の係数保存を用いる。
規約：KST §5、係数は f により標的環へ移る。
使われ方：分母消去式を標的の通常の局所化へ移す。
-/
@[simp] theorem chartToLocalizedTarget_base (r : R) :
    chartToLocalizedTarget I f a (chartBaseMap I a r) =
      algebraMap S (Localization.Away (f a.1)) (f r) := by
  simp [chartToLocalizedTarget, Localization.awayMap, IsLocalization.Away.map]

/--
概要：中心の像が f(a) により生成されるなら、チャートの局所化内の像は標的環から来る。
方針：分子の Iⁿ への所属と像中心の単項生成から f(a)ⁿ を消去する。
規約：KST §5、ここでは f(a) の非零因子性を仮定しない。
使われ方：非零因子の場合に実際の持ち上げ準同型を作る。
-/
theorem chartToLocalizedTarget_mem_range (hI : I.map f = Ideal.span {f a.1})
    (z : BlowupChartRing I a) :
    chartToLocalizedTarget I f a z ∈
      (algebraMap S (Localization.Away (f a.1))).range := by
  obtain ⟨n, r, hr, hz⟩ := chart_clear_denominator_mem I a z
  have hfr : f r ∈ Ideal.span {f a.1 ^ n} := by
    rw [← Ideal.span_singleton_pow, ← hI, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem f hr
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp hfr
  refine ⟨s, ?_⟩
  have heq := congrArg (chartToLocalizedTarget I f a) hz
  rw [map_mul, map_pow, chartToLocalizedTarget_base, chartToLocalizedTarget_base] at heq
  have hu : IsUnit (algebraMap S (Localization.Away (f a.1)) (f a.1) ^ n) :=
    (IsLocalization.Away.algebraMap_isUnit _).pow n
  apply hu.mul_left_inj.mp
  rw [heq, ← map_pow, ← map_mul, hs]

/--
概要：標的で f(a) が正則で像中心を生成するときのチャート持ち上げ準同型。
方針：標的環の正則な局所化をその像と同型にし、チャートの像をその部分環へ制限する。
規約：KST §5、実際の環準同型を普遍性に渡す。
使われ方：blowup の標準チャートへの局所的な普遍写像。
-/
def chartRegularLift (hreg : f a.1 ∈ nonZeroDivisors S)
    (hI : I.map f = Ideal.span {f a.1}) : BlowupChartRing I a →+* S := by
  let hι := IsLocalization.injective (Localization.Away (f a.1))
    (Submonoid.powers_le.mpr hreg)
  let e := RingEquiv.ofLeftInverse hι.hasLeftInverse.choose_spec
  exact e.symm.toRingHom.comp
    ((chartToLocalizedTarget I f a).codRestrict
      (algebraMap S (Localization.Away (f a.1))).range
      (chartToLocalizedTarget_mem_range I f a hI))

/--
概要：正則なチャート持ち上げを局所化すると元の分数写像に戻る。
方針：標的環と局所化内の像の同型の逆写像の恒等式を使う。
規約：KST §5、局所化への単射を介した等式。
使われ方：持ち上げの係数保存と一意性。
-/
@[simp] theorem chartRegularLift_localize (hreg : f a.1 ∈ nonZeroDivisors S)
    (hI : I.map f = Ideal.span {f a.1}) (z : BlowupChartRing I a) :
    algebraMap S (Localization.Away (f a.1)) (chartRegularLift I f a hreg hI z) =
      chartToLocalizedTarget I f a z := by
  let hι := IsLocalization.injective (Localization.Away (f a.1))
    (Submonoid.powers_le.mpr hreg)
  let e := RingEquiv.ofLeftInverse hι.hasLeftInverse.choose_spec
  exact congrArg Subtype.val (e.apply_symm_apply
    ⟨chartToLocalizedTarget I f a z, chartToLocalizedTarget_mem_range I f a hI z⟩)

/--
概要：正則なチャート持ち上げは指定された基底環準同型を延長する。
方針：正則局所化の単射性と分数写像の係数保存を用いる。
規約：KST §5、標的環内での等式。
使われ方：Spec による持ち上げが基底上の射であることの証明。
-/
@[simp] theorem chartRegularLift_base (hreg : f a.1 ∈ nonZeroDivisors S)
    (hI : I.map f = Ideal.span {f a.1}) (r : R) :
    chartRegularLift I f a hreg hI (chartBaseMap I a r) = f r := by
  apply IsLocalization.injective (Localization.Away (f a.1))
    (Submonoid.powers_le.mpr hreg)
  rw [chartRegularLift_localize, chartToLocalizedTarget_base]

/--
概要：正則な生成元を保つチャートからの環準同型は係数写像で一意に定まる。
方針：各元の斉次分母を払い、正則な生成元の冪を消去する。
規約：KST §5、像中心の単項性を一意性には仮定しない。
使われ方：blowup の局所的な普遍性。
-/
theorem chart_hom_ext_of_regular (hreg : f a.1 ∈ nonZeroDivisors S)
    (g h : BlowupChartRing I a →+* S)
    (hg : ∀ r, g (chartBaseMap I a r) = f r)
    (hh : ∀ r, h (chartBaseMap I a r) = f r) : g = h := by
  ext z
  obtain ⟨n, r, _, hz⟩ := chart_clear_denominator_mem I a z
  have eg := congrArg g hz
  have eh := congrArg h hz
  simp only [map_mul, map_pow, hg] at eg
  simp only [map_mul, map_pow, hh] at eh
  have hpow := (nonZeroDivisors S).pow_mem hreg n
  apply sub_eq_zero.mp
  apply (mem_nonZeroDivisors_iff_left.mp hpow) (g z - h z)
  rw [mul_comm, sub_mul, eg, eh, sub_self]

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
