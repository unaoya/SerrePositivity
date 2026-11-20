module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.ChartLocalization

/-!
概要：KST §5 の標準 blowup チャート環を基礎環の局所化の部分環として記述する。
方針：チャート上の a の非零因子性から局所化への単射を得る。
規約：a は基礎環内では非零因子である必要はない。
使われ方：正の冪の blowup と Huneke–Swanson 8.1.5・8.2.1 のチャート比較。
-/

@[expose] public noncomputable section

universe u

namespace SerrePositivity.AlgebraicGeometry

open HomogeneousLocalization

variable {R : Type u} [CommRing R] (I : Ideal R)

/--
概要：標準 blowup チャート環から基礎環の R[1/a] への準同型。
方針：チャート内で a を可逆化し、構成済みの局所化同型で移す。
規約：KST §5、分数 b/a は通常の局所化の分数へ送られる。
使われ方：異なる中心を持つ blowup チャートの像を同じ局所化の中で比較する。
-/
def chartToBaseLocalization (a : I) : BlowupChartRing I a →+* Localization.Away a.1 :=
  (chartAwayEquiv I a).symm.toRingHom.comp
    (algebraMap (BlowupChartRing I a) (BlowupChartAway I a))

/--
概要：標準 blowup チャート環は R[1/a] に単射で埋め込まれる。
方針：チャートで a が非零因子なので、その冪での局所化は単射。
規約：KST §5、R[1/a] が自明環になる場合も含む。
使われ方：チャートの同型を局所化内の部分環の一致から構成する。
-/
theorem chartToBaseLocalization_injective (a : I) :
    Function.Injective (chartToBaseLocalization I a) :=
  (chartAwayEquiv I a).symm.injective.comp
    (IsLocalization.injective (BlowupChartAway I a)
      (Submonoid.powers_le.mpr (chartBaseMap_mem_nonZeroDivisors I a)))

/--
概要：チャートの局所化への埋め込みは基礎環の係数写像を保つ。
方針：局所化同型の係数保存を逆向きに使う。
規約：KST §5、始域の係数はチャートの `chartBaseMap` で表す。
使われ方：チャートの像を I^n/a^n の分数で判定する。
-/
@[simp] theorem chartToBaseLocalization_base (a : I) (r : R) :
    chartToBaseLocalization I a (chartBaseMap I a r) =
      algebraMap R (Localization.Away a.1) r := by
  change (chartAwayEquiv I a).symm
    (algebraMap (BlowupChartRing I a) (BlowupChartAway I a) (chartBaseMap I a r)) = _
  apply (chartAwayEquiv I a).injective
  rw [RingEquiv.apply_symm_apply, chartAwayEquiv_apply_base]
  rfl

/--
概要：チャートの像は、I^n に属する分子を a^n で割った元全体。
方針：順方向は斉次分母消去、逆方向は対応する Rees 単項式の分数を作る。
規約：KST §5、通常の局所化の中で分母を払った等式を使う。
使われ方：Bl_{I^n} と Bl_I のチャートの比較。
-/
theorem mem_chartToBaseLocalization_range_iff (a : I) (z : Localization.Away a.1) :
    z ∈ (chartToBaseLocalization I a).range ↔
      ∃ (n : ℕ) (r : R), r ∈ I ^ n ∧
        z * algebraMap R (Localization.Away a.1) a.1 ^ n =
          algebraMap R (Localization.Away a.1) r := by
  constructor
  · rintro ⟨w, rfl⟩
    obtain ⟨n, r, hr, hw⟩ := chart_clear_denominator_mem I a w
    refine ⟨n, r, hr, ?_⟩
    simpa only [map_mul, map_pow, chartToBaseLocalization_base] using
      congrArg (chartToBaseLocalization I a) hw
  · rintro ⟨n, r, hr, hz⟩
    let p := reesMonomial I n ⟨r, hr⟩
    let w := Away.mk (reesGrade I) (reesDegreeOne_mem I a) n p
      (by simpa using reesMonomial_mem I n ⟨r, hr⟩)
    have hw : chartToBaseLocalization I a w *
        algebraMap R (Localization.Away a.1) a.1 ^ n =
          algebraMap R (Localization.Away a.1) r := by
      have h := congrArg (chartToBaseLocalization I a)
        (chart_mk_clear_denominator I a n p (reesMonomial_mem I n ⟨r, hr⟩))
      simpa only [map_mul, map_pow, chartToBaseLocalization_base, w, p, reesMonomial,
        Polynomial.coeff_monomial_same] using h
    refine ⟨w, ?_⟩
    exact ((IsLocalization.Away.algebraMap_isUnit a.1
      (S := Localization.Away a.1)).pow n).mul_left_inj.mp (hw.trans hz.symm)

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
