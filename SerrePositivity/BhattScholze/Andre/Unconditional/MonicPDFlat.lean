module

public import SerrePositivity.BhattScholze.Andre.PowerRootMonicPDFlat
public import SerrePositivity.BhattScholze.Andre.PerfectPrismVarpiNativePDFlat

/-!
# 原典の R/ϖ における標数条件の自動供給

## 概要
PowerRootMonicPDFlat の hpR は p 正則性ではなく p=0 を意味する。
BS Rem 7.15(1)（著者版 p.62）の R/ϖ ではこの条件を内部で供給できる。

## 方針
(ϖ^p)=(p) から p∈(ϖ) を得て、既存の自由性・忠実平坦性を適用する。

## 規約
prism 商の p 正則性や非零性を追加しない。

## 使われ方
係数条件を呼出し側へ残さず、原典の通常分冪環の平坦性を使う。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Andre
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
local notation "R" => A ⧸ W.ideal
local notation "Rv" => R ⧸ Ideal.span {perfectPrismVarpi W hW}
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "Nv" => PowerRootPolynomial Rv p hp
local notation "bv" => RingHom.comp (Ideal.Quotient.mk (Ideal.span {perfectPrismVarpi W hW}))
  (Ideal.Quotient.mk W.ideal)

/-- 概要：原典の R/ϖ では p が零。
方針：(ϖ^p)=(p) と (ϖ^p)⊆(ϖ) を組み合わせる。
規約：prism 商の p 正則性は不要。
使われ方：BS Rem 7.15(1)（著者版 p.62）の通常分冪表示への標数条件の供給。 -/
theorem perfectPrismVarpiQuotient_prime_eq_zero_of_unconditional : (p : Rv) = 0 := by
  have hle : Ideal.span {perfectPrismVarpi W hW ^ p} ≤
      Ideal.span {perfectPrismVarpi W hW} := by
    apply Ideal.span_le.mpr
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    exact Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self _) p
      (Nat.Prime.pos (Fact.out : p.Prime))
  rw [perfectPrismVarpi_span_pow W hW] at hle
  have hm := hle (Ideal.mem_span_singleton_self (p : R))
  simpa only [map_natCast] using Ideal.Quotient.eq_zero_iff_mem.mpr hm

/-- 概要：R/ϖ 上のモニック無限根分冪表示環は自由。
方針：原典の係数商の p=0 を内部で証明して既存の自由性へ渡す。
規約：正次数も prism 商の p 正則性も不要。
使われ方：BS Rem 7.15(1)（著者版 p.62）の実係数環上の自由性。 -/
theorem powerRootMonicDPPresentation_free_of_unconditional
    (f : Polynomial A) (hf : f.Monic) :
    Module.Free Rv (PrincipalDPPresentation Nv
      (powerRootPolynomialBaseMap Rv p hp (f.map bv))) :=
  powerRootMonicDPPresentation_free Rv p hp (Fact.out : p.Prime)
    (perfectPrismVarpiQuotient_prime_eq_zero_of_unconditional W hW) (f.map bv) (hf.map bv)

/-- 概要：R/ϖ 上の正次数モニック無限根分冪表示環は忠実平坦。
方針：p=0 と、係数商後のモニック性・正次数を既存の忠実平坦性へ供給する。
規約：原典の正次数条件を保持し、非零性を追加しない。
使われ方：BS Rem 7.15(1)（著者版 p.62）の通常代数の忠実平坦性。 -/
theorem powerRootMonicDPPresentation_faithfullyFlat_of_unconditional
    (f : Polynomial A) (hf : f.Monic) (hdeg : 0 < f.natDegree) :
    Module.FaithfullyFlat Rv (PrincipalDPPresentation Nv
      (powerRootPolynomialBaseMap Rv p hp (f.map bv))) :=
  perfectPrismVarpiNativePDEnvelope_faithfullyFlat W hW f hf hdeg

end SerrePositivity.BhattScholze.Andre
