module

public import SerrePositivity.AlgebraicGeometry.ChartAlgebra

/-!
概要：KST §5 の標準 blowup チャートを中心の補集合で局所化する。
方針：斉次分数の分母を払い、係数環の通常の局所化と比較する。
規約：基礎環と中心に Noether 性を仮定しない。
使われ方：blowup が中心の補開集合上で同型になることの局所計算。
-/

@[expose] public noncomputable section

universe u

namespace SerrePositivity.AlgebraicGeometry

open Polynomial HomogeneousLocalization

variable {R : Type u} [CommRing R] (I : Ideal R)

/--
概要：Rees の次数一生成元の n 乗は a^n t^n。
方針：単項式の冪の公式を使う。
規約：KST §5 の通常の Rees 次数。
使われ方：標準チャートの分母と係数環の冪を対応させる。
-/
@[simp] lemma reesDegreeOne_pow_val (a : I) (n : ℕ) :
    ((reesDegreeOne I a ^ n : reesAlgebra I) : R[X]) = monomial n (a.1 ^ n) := by
  simp [reesDegreeOne, reesMonomial, monomial_pow]

/--
概要：標準チャートの斉次分数の分母を指定した a の冪で払う。
方針：斉次な分子 p を単項式に書き、同じ分母の局所化で比較する。
規約：KST §5、分子の次数 n と分母の指数を明示する。
使われ方：分子の係数が I^n に属することを保ったチャート環の記述。
-/
lemma chart_mk_clear_denominator (a : I) (n : ℕ) (p : reesAlgebra I)
    (hp : p ∈ reesGrade I n) :
    Away.mk (reesGrade I) (reesDegreeOne_mem I a) n p (by simpa using hp) *
      chartBaseMap I a a.1 ^ n = chartBaseMap I a (p.1.coeff n) := by
  apply HomogeneousLocalization.val_injective
  rw [val_mul, val_pow, chartBaseMap_val, chartBaseMap_val]
  simp only [Away.val_mk, Localization.mk_eq_mk', ← map_pow]
  rw [mul_comm, IsLocalization.mul_mk'_eq_mk'_of_mul,
    ← IsLocalization.mk'_one (M := Submonoid.powers (reesDegreeOne I a))
      (Localization.Away (reesDegreeOne I a)) (algebraMap R (reesAlgebra I) (p.1.coeff n))]
  apply IsLocalization.mk'_eq_iff_eq.mpr
  congr 1
  apply Subtype.ext
  change (1 : R[X]) * (C (a.1 ^ n) * (p : R[X])) =
    (reesDegreeOne I a ^ n : reesAlgebra I).val * C (p.1.coeff n)
  rw [one_mul, reesDegreeOne_pow_val,
    (mem_reesGrade_iff I n p).mp (by simpa using hp)]
  simp only [coeff_monomial_same, C_mul_monomial, monomial_mul_C]

/--
概要：標準チャートの元は、I^n に属する分子の係数と a^n で表示できる。
方針：斉次分数表示を取り、指定次数での分母消去を適用する。
規約：KST §5、分子係数の I^n への所属を結論に含める。
使われ方：イデアルの冪を変えた blowup のチャートの像を比較する。
-/
theorem chart_clear_denominator_mem (a : I) (z : BlowupChartRing I a) :
    ∃ (n : ℕ) (r : R), r ∈ I ^ n ∧
      z * chartBaseMap I a a.1 ^ n = chartBaseMap I a r := by
  obtain ⟨n, p, hp, rfl⟩ := Away.mk_surjective (reesGrade I) (reesDegreeOne_mem I a) z
  exact ⟨n, p.1.coeff n, p.2 n, chart_mk_clear_denominator I a n p (by simpa using hp)⟩

/--
概要：標準チャートの任意の元は a の冪で分母を払うと基礎環の像になる。
方針：分子の所属を保つ分母消去から係数の所属条件を忘れる。
規約：KST §5、消去する指数は元に依存してよい。
使われ方：中心の補集合上の構造準同型が局所化であることを示す。
-/
theorem chart_clear_denominator (a : I) (z : BlowupChartRing I a) :
    ∃ (n : ℕ) (r : R), z * chartBaseMap I a a.1 ^ n = chartBaseMap I a r := by
  obtain ⟨n, r, _, h⟩ := chart_clear_denominator_mem I a z
  exact ⟨n, r, h⟩

/--
概要：チャートの係数写像で等しい二元は a のある冪を掛けると基礎環で等しい。
方針：通常の Rees 局所化での等式を分母で払い、該当次数の係数を取る。
規約：KST §5、環準同型の単射性や a の非零因子性は仮定しない。
使われ方：係数環の局所化の等式判定を検証する。
-/
theorem chartBaseMap_eq_iff (a : I) (r s : R) :
    chartBaseMap I a r = chartBaseMap I a s ↔ ∃ n : ℕ, a.1 ^ n * r = a.1 ^ n * s := by
  constructor
  · intro h
    have h' := congrArg val h
    rw [chartBaseMap_val, chartBaseMap_val,
      IsLocalization.eq_iff_exists (Submonoid.powers (reesDegreeOne I a))] at h'
    obtain ⟨⟨_, n, rfl⟩, hn⟩ := h'
    refine ⟨n, ?_⟩
    have hc := congrArg (fun p : reesAlgebra I => (p : R[X]).coeff n) hn
    simpa [reesDegreeOne, reesMonomial, monomial_pow, coeff_mul_C] using hc
  · rintro ⟨n, hn⟩
    apply HomogeneousLocalization.val_injective
    rw [chartBaseMap_val, chartBaseMap_val,
      IsLocalization.eq_iff_exists (Submonoid.powers (reesDegreeOne I a))]
    refine ⟨⟨reesDegreeOne I a ^ n, n, rfl⟩, ?_⟩
    apply Subtype.ext
    change (reesDegreeOne I a ^ n : reesAlgebra I).val * C r =
      (reesDegreeOne I a ^ n : reesAlgebra I).val * C s
    simp only [reesDegreeOne_pow_val, monomial_mul_C, hn]

/--
概要：標準チャートで a を可逆化すると、基礎環を a で局所化した環になる。
方針：チャートでの分母消去と等式判定を通常の局所化の普遍条件に代入する。
規約：KST §5、局所化の任意の実現 S と実際の準同型 f について述べる。
使われ方：補開集合 D(a) 上で blowup 構造射が同型であることの環論的入力。
-/
theorem chart_localization_isLocalizationMap (a : I)
    {S : Type*} [CommRing S] (f : BlowupChartRing I a →+* S)
    (hf : (Submonoid.powers (chartBaseMap I a a.1)).IsLocalizationMap f) :
    (Submonoid.powers a.1).IsLocalizationMap (f.comp (chartBaseMap I a)) where
  map_units := by
    rintro ⟨_, n, rfl⟩
    simpa only [RingHom.comp_apply, map_pow] using
      hf.map_units ⟨chartBaseMap I a a.1 ^ n, n, rfl⟩
  surj z := by
    obtain ⟨⟨c, ⟨_, n, rfl⟩⟩, hc⟩ := hf.surj z
    obtain ⟨m, r, hr⟩ := chart_clear_denominator I a c
    refine ⟨⟨r, ⟨a.1 ^ (n + m), n + m, rfl⟩⟩, ?_⟩
    change z * f (chartBaseMap I a (a.1 ^ (n + m))) = f (chartBaseMap I a r)
    simp only [map_pow] at hc ⊢
    calc
      _ = (z * f (chartBaseMap I a a.1) ^ n) *
          f (chartBaseMap I a a.1) ^ m := by rw [pow_add, mul_assoc]
      _ = f c * f (chartBaseMap I a a.1) ^ m := by rw [hc]
      _ = f (c * chartBaseMap I a a.1 ^ m) := by rw [map_mul, map_pow]
      _ = f (chartBaseMap I a r) := congrArg f hr
  exists_of_eq := by
    intro r s h
    obtain ⟨⟨_, n, rfl⟩, hn⟩ := hf.exists_of_eq h
    have hbase : chartBaseMap I a (a.1 ^ n * r) = chartBaseMap I a (a.1 ^ n * s) := by
      simpa only [map_mul, map_pow] using hn
    obtain ⟨m, hm⟩ := (chartBaseMap_eq_iff I a _ _).mp hbase
    refine ⟨⟨a.1 ^ (m + n), m + n, rfl⟩, ?_⟩
    simpa only [pow_add, mul_assoc] using hm

/--
概要：標準チャート内の a を可逆化した具体的な環。
方針：Mathlib の通常の単元局所化を取る。
規約：KST §5、次数一元 a t の局所化を既に取った後に a を可逆化する。
使われ方：中心の補開集合のアフィンチャート。
-/
abbrev BlowupChartAway (a : I) := Localization.Away (chartBaseMap I a a.1)

/--
概要：基礎環から補開集合上の blowup チャート環への係数写像。
方針：チャートの係数写像と通常の局所化の写像を合成する。
規約：KST §5、始域は元の基礎環 R。
使われ方：R[1/a] との同型の基準準同型。
-/
def chartAwayBaseMap (a : I) : R →+* BlowupChartAway I a :=
  (algebraMap (BlowupChartRing I a) (BlowupChartAway I a)).comp (chartBaseMap I a)

/--
概要：補開集合上のチャート環は基礎環の a における局所化を実現する。
方針：通常のチャート局所化に普遍条件の比較定理を適用する。
規約：KST §5、環の実現と係数写像を明示した局所化条件。
使われ方：R[1/a] とチャート環の局所化との実際の環同型。
-/
theorem chartAwayBaseMap_isLocalizationMap (a : I) :
    (Submonoid.powers a.1).IsLocalizationMap (chartAwayBaseMap I a) :=
  chart_localization_isLocalizationMap I a _
    (IsLocalization.toLocalizationMap (Submonoid.powers (chartBaseMap I a a.1))
      (BlowupChartAway I a)).isLocalizationMap

/--
概要：基礎環の R[1/a] と補開集合上の標準 blowup チャート環の環同型。
方針：両方が同じ準同型の局所化を実現することから普遍性で同定する。
規約：KST §5、同型は基礎環 R からの係数写像を保つ。
使われ方：中心の補開集合上のスキーム同型の局所モデル。
-/
def chartAwayEquiv (a : I) : Localization.Away a.1 ≃+* BlowupChartAway I a := by
  letI : Algebra R (BlowupChartAway I a) := (chartAwayBaseMap I a).toAlgebra
  letI : IsLocalization.Away a.1 (BlowupChartAway I a) :=
    (isLocalization_iff_isLocalizationMap _ _).mpr (chartAwayBaseMap_isLocalizationMap I a)
  exact (IsLocalization.algEquiv (Submonoid.powers a.1)
    (Localization.Away a.1) (BlowupChartAway I a)).toRingEquiv

/--
概要：補開集合上のチャート環同型は基礎環の係数を保つ。
方針：局所化の代数同型の係数保存則を使う。
規約：KST §5、局所化間の同型を基底上の同型として使う。
使われ方：Spec を適用した際の構造射の交換式。
-/
@[simp] theorem chartAwayEquiv_apply_base (a : I) (r : R) :
    chartAwayEquiv I a (algebraMap R (Localization.Away a.1) r) = chartAwayBaseMap I a r := by
  let : Algebra R (BlowupChartAway I a) := (chartAwayBaseMap I a).toAlgebra
  let : IsLocalization.Away a.1 (BlowupChartAway I a) :=
    (isLocalization_iff_isLocalizationMap _ _).mpr (chartAwayBaseMap_isLocalizationMap I a)
  exact (IsLocalization.algEquiv (Submonoid.powers a.1)
    (Localization.Away a.1) (BlowupChartAway I a)).commutes r

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
