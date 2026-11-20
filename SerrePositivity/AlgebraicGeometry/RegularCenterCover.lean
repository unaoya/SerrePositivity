module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.ChartRegularLift
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
概要：KST §5 の blowup の普遍性に使う、正則な単項像中心の基本開被覆。
方針：f(a) = b s の係数 s が単位イデアルを生成することを正則性から示す。
規約：中心の有限生成性と Noether 性を使わない。
使われ方：任意の正則な単項生成元から、中心の元の像で生成される局所モデルへ移る。
-/

@[expose] public noncomputable section

universe u v
namespace SerrePositivity.AlgebraicGeometry
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
  (I : Ideal R) (f : R →+* S) (b : S)

/--
概要：正則な像中心生成元 b に対する局所的な生成係数の集合。
方針：中心の元 a の像を b s と表示する係数 s を全て取る。
規約：KST §5、係数の一意性は定義には不要。
使われ方：正則な単項像中心の基本開被覆の添字。
-/
def regularCenterCoefficients : Set S := {s | ∃ a : I, f a.1 = b * s}

/--
概要：像中心が正則な b で生成されるなら生成係数は単位イデアルを生成する。
方針：像中心を (b) と係数イデアルの積に入れ、b の正則性で一元を得る。
規約：KST §5、有限生成性や体上という仮定を置かない。
使われ方：係数に対応する基本開集合の被覆性。
-/
theorem span_regularCenterCoefficients (hreg : b ∈ nonZeroDivisors S)
    (hI : I.map f = Ideal.span {b}) :
    Ideal.span (regularCenterCoefficients I f b) = ⊤ := by
  let J := Ideal.span (regularCenterCoefficients I f b)
  have hle : I.map f ≤ Ideal.span {b} * J := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro a ha
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton.mp
      (hI ▸ Ideal.mem_map_of_mem f ha)
    apply Ideal.mem_span_singleton_mul.mpr
    refine ⟨s, Ideal.subset_span ?_, ?_⟩
    · exact ⟨⟨a, ha⟩, by simpa only [mul_comm] using hs⟩
    · simpa only [mul_comm] using hs.symm
  have hb : b ∈ Ideal.span {b} * J :=
    hle (hI.symm ▸ Ideal.subset_span (Set.mem_singleton b))
  obtain ⟨s, hs, heq⟩ := Ideal.mem_span_singleton_mul.mp hb
  have hs1 : s = 1 := by
    apply sub_eq_zero.mp
    apply (mem_nonZeroDivisors_iff_left.mp hreg) (s - 1)
    rw [mul_sub, heq, mul_one, sub_self]
  exact Ideal.eq_top_of_isUnit_mem J (hs1 ▸ hs) isUnit_one

/--
概要：正則な像中心の生成係数に対応する基本開集合は Spec S を覆う。
方針：基本開集合の被覆と単位イデアル生成の同値を使う。
規約：KST §5、生成係数を部分型で添字付けする。
使われ方：中心の元の像を生成元とするチャート持ち上げの貼り合わせ。
-/
theorem iSup_regularCenterCoefficient_basicOpen (hreg : b ∈ nonZeroDivisors S)
    (hI : I.map f = Ideal.span {b}) :
    ⨆ s : regularCenterCoefficients I f b, PrimeSpectrum.basicOpen s.1 = ⊤ := by
  apply PrimeSpectrum.iSup_basicOpen_eq_top_iff.mpr
  rw [Subtype.range_coe_subtype]
  exact span_regularCenterCoefficients I f b hreg hI

/--
概要：生成係数 s を可逆化すると f(a) は正則になる。
方針：局所化で正則性が保存され、可逆な係数との積も正則である。
規約：KST §5、f(a) = b s という表示を明示する。
使われ方：基本開集合ごとの正則チャート持ち上げ。
-/
theorem regularCenter_localized_regular (hreg : b ∈ nonZeroDivisors S)
    (a : I) (s : S) (hs : f a.1 = b * s) :
    algebraMap S (Localization.Away s) (f a.1) ∈
      nonZeroDivisors (Localization.Away s) := by
  rw [hs, map_mul]
  exact mul_mem (IsLocalization.nonZeroDivisors_le_comap (S := Localization.Away s)
    (Submonoid.powers s) hreg)
    (IsLocalization.Away.algebraMap_isUnit s).mem_nonZeroDivisors

/--
概要：生成係数 s を可逆化すると像中心は f(a) の像で生成される。
方針：中心の写像の合成則と、単元倍で単項イデアルが変わらないことを使う。
規約：KST §5、局所化環でのイデアルの等式。
使われ方：基本開集合ごとのチャート持ち上げの存在条件。
-/
theorem regularCenter_localized_image (hI : I.map f = Ideal.span {b})
    (a : I) (s : S) (hs : f a.1 = b * s) :
    I.map ((algebraMap S (Localization.Away s)).comp f) =
      Ideal.span {algebraMap S (Localization.Away s) (f a.1)} := by
  rw [← Ideal.map_map, hI, Ideal.map_span, Set.image_singleton, hs, map_mul]
  exact (Ideal.span_singleton_mul_right_unit
    (IsLocalization.Away.algebraMap_isUnit s) _).symm

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
