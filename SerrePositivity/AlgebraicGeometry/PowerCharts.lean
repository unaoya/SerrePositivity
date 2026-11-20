module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.ChartEmbedding

/-!
概要：KST §5、特に (5.10) の正の冪による blowup の標準チャート比較。
方針：チャート環を一つの通常の局所化に埋め込み、その像を冪ごとの分子で比較する。
規約：中心の冪 n は正とする。
使われ方：Bl_{I^n} と Bl_I の同型、および Lemma 5.6 の古典的入力。
-/

@[expose] public noncomputable section

universe u

namespace SerrePositivity.AlgebraicGeometry

variable {R : Type u} [CommRing R]

/--
概要：a^n での局所化と a での局所化は、n が正なら基礎環上で同型。
方針：a^n が単元なら a も単元なので、両局所化の普遍性を使う。
規約：KST §5 の冪比較、n = 0 を除外する。
使われ方：冪中心のチャートを同じ R[1/a] の部分環として比較する。
-/
def awayPowEquiv (a : R) (n : ℕ) (hn : 0 < n) :
    Localization.Away (a ^ n) ≃ₐ[R] Localization.Away a := by
  have hu : IsUnit (algebraMap R (Localization.Away (a ^ n)) a) := by
    apply (isUnit_pow_iff hn.ne').mp
    rw [← map_pow]
    exact IsLocalization.Away.algebraMap_isUnit (a ^ n)
  letI : IsLocalization.Away a (Localization.Away (a ^ n)) :=
    IsLocalization.of_le (M := Submonoid.powers (a ^ n)) (Submonoid.powers a)
      (Submonoid.powers_le.mpr ⟨n, rfl⟩) (fun x hx => by
        obtain ⟨k, rfl⟩ := hx
        simpa only [map_pow] using hu.pow k)
  exact IsLocalization.algEquiv (Submonoid.powers a)
    (Localization.Away (a ^ n)) (Localization.Away a)

/--
概要：正の冪による局所化同型は基礎環の係数を保つ。
方針：局所化の代数同型の係数保存を使う。
規約：KST §5、(5.10) の基底上の比較に用いる。
使われ方：冪中心のチャート埋め込みの係数計算。
-/
@[simp] theorem awayPowEquiv_apply_base (a : R) (n : ℕ) (hn : 0 < n) (r : R) :
    awayPowEquiv a n hn (algebraMap R (Localization.Away (a ^ n)) r) =
      algebraMap R (Localization.Away a) r :=
  (awayPowEquiv a n hn).commutes r

variable (I : Ideal R)

/--
概要：中心 I の元 a から I^n の元 a^n を作る。
方針：イデアルの冪の所属を使う。
規約：KST §5、元の冪とイデアルの冪を区別する。
使われ方：冪中心の標準チャートの添字。
-/
def powerCenterElement (a : I) (n : ℕ) : ↥(I ^ n) :=
  ⟨a.1 ^ n, Ideal.pow_mem_pow a.2 n⟩

/--
概要：冪中心 I^n の a^n チャート環を R[1/a] に送る。
方針：そのチャートの R[1/a^n] への埋め込みと局所化の冪比較を合成する。
規約：KST §5、n は正である。
使われ方：元の中心 I の a チャートとの像の比較。
-/
def powerChartToBaseLocalization (a : I) (n : ℕ) (hn : 0 < n) :
    BlowupChartRing (I ^ n) (powerCenterElement I a n) →+* Localization.Away a.1 :=
  (awayPowEquiv a.1 n hn).toRingHom.comp
    (chartToBaseLocalization (I ^ n) (powerCenterElement I a n))

/--
概要：冪中心のチャート環から R[1/a] への写像も単射。
方針：チャートの単射と局所化の環同型を合成する。
規約：KST §5、a の基礎環での非零因子性は不要。
使われ方：共通の局所化の中でのチャート環の同型構成。
-/
theorem powerChartToBaseLocalization_injective (a : I) (n : ℕ) (hn : 0 < n) :
    Function.Injective (powerChartToBaseLocalization I a n hn) :=
  (awayPowEquiv a.1 n hn).injective.comp
    (chartToBaseLocalization_injective (I ^ n) (powerCenterElement I a n))

/--
概要：冪中心のチャートの共通局所化への埋め込みは係数を保つ。
方針：チャート埋め込みと局所化の冪比較の係数保存を合成する。
規約：KST §5、中心は I^n、基礎環は R のまま。
使われ方：二つのチャート環の像の一致の計算。
-/
@[simp] theorem powerChartToBaseLocalization_base (a : I) (n : ℕ) (hn : 0 < n) (r : R) :
    powerChartToBaseLocalization I a n hn
        (chartBaseMap (I ^ n) (powerCenterElement I a n) r) =
      algebraMap R (Localization.Away a.1) r := by
  change awayPowEquiv a.1 n hn
    (chartToBaseLocalization (I ^ n) (powerCenterElement I a n)
      (chartBaseMap (I ^ n) (powerCenterElement I a n) r)) = _
  rw [chartToBaseLocalization_base]
  exact (awayPowEquiv a.1 n hn).commutes r

set_option backward.isDefEq.respectTransparency false in
/--
概要：冪中心のチャートの像は I^(n m) の元を a^(n m) で割った元全体。
方針：元のチャートの像の判定を、正の冪による局所化同型で移す。
規約：KST §5、m は任意の自然数、n は正。
使われ方：元の中心のチャートの像と比較する。
-/
theorem mem_powerChartToBaseLocalization_range_iff (a : I) (n : ℕ) (hn : 0 < n)
    (z : Localization.Away a.1) :
    z ∈ (powerChartToBaseLocalization I a n hn).range ↔
      ∃ (m : ℕ) (r : R), r ∈ (I ^ n) ^ m ∧
        z * algebraMap R (Localization.Away a.1) a.1 ^ (n * m) =
          algebraMap R (Localization.Away a.1) r := by
  constructor
  · rintro ⟨w, rfl⟩
    obtain ⟨m, r, hr, hw⟩ :=
      chart_clear_denominator_mem (I ^ n) (powerCenterElement I a n) w
    refine ⟨m, r, hr, ?_⟩
    have h := congrArg (powerChartToBaseLocalization I a n hn) hw
    rw [(powerChartToBaseLocalization I a n hn).map_mul,
      (powerChartToBaseLocalization I a n hn).map_pow,
      powerChartToBaseLocalization_base, powerChartToBaseLocalization_base] at h
    simpa only [powerCenterElement, map_pow, pow_mul] using h
  · rintro ⟨m, r, hr, hz⟩
    let e := awayPowEquiv a.1 n hn
    have hmem : e.symm z ∈
        (chartToBaseLocalization (I ^ n) (powerCenterElement I a n)).range := by
      apply (mem_chartToBaseLocalization_range_iff (I ^ n) (powerCenterElement I a n) _).mpr
      refine ⟨m, r, hr, ?_⟩
      apply e.injective
      simpa only [e, map_mul, map_pow, AlgEquiv.apply_symm_apply, AlgEquiv.commutes,
        powerCenterElement, pow_mul] using hz
    obtain ⟨w, hw⟩ := hmem
    refine ⟨w, ?_⟩
    exact (congrArg e hw).trans (e.apply_symm_apply z)

/--
概要：元の中心とその正の冪の対応するチャート環は、R[1/a] 内で同じ像を持つ。
方針：分子・分母に a^(n m-m) を補い、分母の指数を n の倍数にする。
規約：KST §5、(5.10)。Noether 性も有限生成性も不要。
使われ方：対応する標準チャートの実際の環同型の構成。
-/
theorem powerChart_range_eq (a : I) (n : ℕ) (hn : 0 < n) :
    (chartToBaseLocalization I a).range = (powerChartToBaseLocalization I a n hn).range := by
  ext z
  rw [mem_chartToBaseLocalization_range_iff, mem_powerChartToBaseLocalization_range_iff]
  constructor
  · rintro ⟨m, r, hr, hz⟩
    have hm : m ≤ n * m := by nlinarith
    have hexp : m + (n * m - m) = n * m := Nat.add_sub_of_le hm
    refine ⟨m, r * a.1 ^ (n * m - m), ?_, ?_⟩
    · have hmul : r * a.1 ^ (n * m - m) ∈ I ^ (m + (n * m - m)) := by
        rw [pow_add]
        exact Ideal.mul_mem_mul hr (Ideal.pow_mem_pow a.2 _)
      simpa only [hexp, ← pow_mul] using hmul
    · calc
        _ = z * algebraMap R (Localization.Away a.1) a.1 ^ (m + (n * m - m)) := by rw [hexp]
        _ = (z * algebraMap R (Localization.Away a.1) a.1 ^ m) *
            algebraMap R (Localization.Away a.1) a.1 ^ (n * m - m) := by
          rw [pow_add, mul_assoc]
        _ = algebraMap R (Localization.Away a.1) (r * a.1 ^ (n * m - m)) := by
          rw [hz, map_mul, map_pow]
  · rintro ⟨m, r, hr, hz⟩
    exact ⟨n * m, r, by simpa only [← pow_mul] using hr, hz⟩

/--
概要：I の a チャートと I^n の a^n チャートの実際の環同型。
方針：共通の R[1/a] への単射の像が一致することを使う。
規約：KST §5、(5.10)。n は正で、同型は基礎環の係数を保つ。
使われ方：正の冪による blowup 同型を標準チャートごとに構成する。
-/
def powerChartEquiv (a : I) (n : ℕ) (hn : 0 < n) :
    BlowupChartRing I a ≃+* BlowupChartRing (I ^ n) (powerCenterElement I a n) :=
  (RingEquiv.ofLeftInverse (chartToBaseLocalization_injective I a).hasLeftInverse.choose_spec).trans
    ((RingEquiv.subringCongr (powerChart_range_eq I a n hn)).trans
      (RingEquiv.ofLeftInverse
        (powerChartToBaseLocalization_injective I a n hn).hasLeftInverse.choose_spec).symm)

/--
概要：冪チャートの同型は共通の局所化への埋め込みと両立する。
方針：単射をその像への環同型にした際の逆写像の法則を使う。
規約：KST §5、(5.10) のチャート比較は R[1/a] の中の一致として構成する。
使われ方：重なり上の比較と係数保存の証明。
-/
@[simp] theorem powerChartEquiv_into_localization (a : I) (n : ℕ) (hn : 0 < n)
    (z : BlowupChartRing I a) :
    powerChartToBaseLocalization I a n hn (powerChartEquiv I a n hn z) =
      chartToBaseLocalization I a z := by
  let e₀ := RingEquiv.ofLeftInverse
    (chartToBaseLocalization_injective I a).hasLeftInverse.choose_spec
  let e₁ := RingEquiv.ofLeftInverse
    (powerChartToBaseLocalization_injective I a n hn).hasLeftInverse.choose_spec
  exact congrArg Subtype.val (e₁.apply_symm_apply
    (RingEquiv.subringCongr (powerChart_range_eq I a n hn) (e₀ z)))

/--
概要：冪による標準チャートの同型は基礎環の係数を固定する。
方針：共通の局所化への単射を通して係数保存を判定する。
規約：KST §5、(5.10) の同型は基底上で使う。
使われ方：Spec を取ったチャート同型と構造射の交換式。
-/
@[simp] theorem powerChartEquiv_base (a : I) (n : ℕ) (hn : 0 < n) (r : R) :
    powerChartEquiv I a n hn (chartBaseMap I a r) =
      chartBaseMap (I ^ n) (powerCenterElement I a n) r := by
  apply powerChartToBaseLocalization_injective I a n hn
  rw [powerChartEquiv_into_localization, chartToBaseLocalization_base,
    powerChartToBaseLocalization_base]

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
