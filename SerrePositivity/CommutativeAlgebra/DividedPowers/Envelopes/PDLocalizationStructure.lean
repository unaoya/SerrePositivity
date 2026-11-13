module

public import SerrePositivity.CommutativeAlgebra.DividedPowers.Envelopes.PDLocalizationAddition

/-!
# 局所化への分冪構造の一意な延長

## 概要
局所化イデアルに分冪構造を載せ、元の環からの写像が分冪射となることと一意性を示す。

## 方針
分数公式で証明した全公理を束ね、任意の延長を分母の斉次性で判定する。

## 規約
任意の乗法的集合を扱う。原像のイデアルの正則性は仮定しない。

## 使われ方
Berthelot I.1.7.1、III.4、Stacks 07HN。結晶厚化の Zariski 局所化。
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.BhattScholze.Prismatic.PDLocalizationDpow
variable {R : Type u} [CommRing R] (M : Submonoid R)
variable (S : Type u) [CommRing S] [Algebra R S] [IsLocalization M S]
variable {I : Ideal R} (δ : DividedPowers I)

/-- 分数公式による局所化イデアルの分冪構造。 -/
def localizationDividedPowers : DividedPowers (I.map (algebraMap R S)) where
  dpow := localizationDpow M S δ
  dpow_null := localizationDpow_null M S δ
  dpow_zero := localizationDpow_zero M S δ
  dpow_one := localizationDpow_one M S δ
  dpow_mem := localizationDpow_mem M S δ
  dpow_add := localizationDpow_add M S δ
  dpow_mul := localizationDpow_mul M S δ
  mul_dpow := localizationDpow_mul_dpow M S δ
  dpow_comp := localizationDpow_comp M S δ

/-- 局所化の標準写像は分冪射。 -/
theorem localization_isDPMorphism :
    δ.IsDPMorphism (localizationDividedPowers M S δ) (algebraMap R S) :=
  ⟨le_rfl, fun {n} _a ha => localizationDpow_algebraMap M S δ n ha⟩

/-- 局所化した分冪構造の実際の分数公式。 -/
theorem localizationDividedPowers_mk (n : ℕ) {a : R} (ha : a ∈ I) (s : M) :
    (localizationDividedPowers M S δ).dpow n (IsLocalization.mk' S a s) =
      IsLocalization.mk' S (δ.dpow n a) (s ^ n) :=
  localizationDpow_mk M S δ n ha s

/-- 元の環の分冪を延長する局所化イデアルの分冪構造は一意。 -/
theorem localizationDividedPowers_unique (ε : DividedPowers (I.map (algebraMap R S)))
    (hε : δ.IsDPMorphism ε (algebraMap R S)) : ε = localizationDividedPowers M S δ := by
  apply DividedPowers.ext
  intro n x hx
  obtain ⟨⟨a, s⟩, h⟩ := (IsLocalization.mem_map_algebraMap_iff M S).mp hx
  have hx' : x = IsLocalization.mk' S (a : R) s := IsLocalization.eq_mk'_iff_mul_eq.mpr h
  rw [hx', localizationDividedPowers_mk M S δ n a.property s]
  apply IsLocalization.eq_mk'_iff_mul_eq.mpr
  rw [SubmonoidClass.coe_pow, map_pow, mul_comm, ← ε.dpow_mul (fraction_mem M S a.property s),
    IsLocalization.mk'_spec']
  exact hε.dpow_comp a a.property

/-- 元の環からの合成が分冪射なら、局所化からの射も分冪射。 -/
theorem localization_isDPMorphism_of_comp {T : Type u} [CommRing T] {L : Ideal T}
    (ε : DividedPowers L) (f : S →+* T) (hf : δ.IsDPMorphism ε (f.comp (algebraMap R S))) :
    (localizationDividedPowers M S δ).IsDPMorphism ε f :=
  DividedPowers.IsDPMorphism.of_comp δ _ ε (algebraMap R S) f rfl
    (localization_isDPMorphism M S δ) hf

end SerrePositivity.BhattScholze.Prismatic.PDLocalizationDpow
