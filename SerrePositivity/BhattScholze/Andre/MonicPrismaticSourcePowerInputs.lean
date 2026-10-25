module

public import SerrePositivity.BhattScholze.Andre.MonicPrismaticCanonicalPowerResidue
public import SerrePositivity.BhattScholze.Prism.Residue.PrismaticResidue
public import SerrePositivity.HomologicalAlgebra.NilpotentDerivedReduction

/-!
# André E1・E2：モニック源の実生成元冪商の G9 入力

## 概要

有限正次数モニック族の実逐次完備化の A/(p,dⁿ) 還元は離散かつ H⁰ が平坦であり、
A/(dⁿ) 還元は p 導来完備で標準 mod p 還元が離散かつ平坦。
BS Rem 7.15（著者版 p.62）の生成元冪商計算。

## 方針

同じ実対象の標準冪零還元に G10 を適用し、一般商比較と G8 の完備性を接続する。
原典の Prop 7.11 を使う証明とは異なる経路の計算。

## 規約

正の冪と元の係数射に沿う実還元を使い、d mod p の正則性は要求しない。

## 使われ方

生成元冪商に G9 を適用し、完備化源の離散性と平坦性を導く。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (f : σ → Polynomial A) (n : ℕ) (hn : 0 < n)
variable (hf : ∀ t, (f t).Monic) (hdeg : ∀ t, 0 < (f t).natDegree)
variable {m : ℕ} (s : Fin m ≃ σ)
variable (hpA : Function.Injective (fun x : A => (p : A) * x))
  (hd : IsSMulRegular A d) (v : Aˣ) (hv : (v : A) = D.delta d)
local notation "Qₙ" => A ⧸ Ideal.span {(p : A), d ^ n}
local notation "Kₙ" => prismaticPowerResidueIdeal (p : A) d n
local notation "X₀" => MonicPrismaticSourceIteratedPDCompletion D d f
local notation "Y₀" => CategoryTheory.Functor.obj
  (boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {(p : A), d ^ n}))) X₀
local notation "Tₙ" => A ⧸ Ideal.span {d ^ n}
local notation "Mₙ" => Tₙ ⧸ Ideal.span {(p : Tₙ)}
local notation "Zₙ" => CategoryTheory.Functor.obj
  (boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {d ^ n}))) X₀
local notation "Wₙ" => CategoryTheory.Functor.obj
  (boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {(p : Tₙ)}))) Zₙ
include hn hf hdeg s hpA hd v hv

/-- 概要：G10により、実A/(p,dⁿ)還元は次数零に集中しH0が平坦。
方針：標準冪零還元の離散・忠実平坦性から G10 を適用し、実合成商比較で標準 mod p 商へ移す。
規約：正の冪 n、有限正次数モニック族、p と d の個別の正則性、δ(d) の単元性を仮定する。
使われ方：BS Rem 7.15（著者版 p.62）の生成元冪商への G9 適用の入力。 -/
theorem monicPrismaticSourcePowerResidue_pure_flat :
    (Y₀).obj.IsGE 0 ∧ (Y₀).obj.IsLE 0 ∧
      Module.Flat Qₙ ((DerivedCategory.homologyFunctor (ModuleCat Qₙ) 0).obj (Y₀).obj) := by
  have hPure := monicPrismaticSourceCanonicalPowerResidue_homology_isZero
    D d f n hn s hf hpA hd v hv
  have hFF := monicPrismaticSourceCanonicalPowerResidueH0_faithfullyFlat
    D d f n hn s hf hdeg hpA hd v hv
  let := hFF
  exact derived_pure_flat_of_nilpotent_reduction Kₙ Y₀ hPure
    inferInstance ⟨n, prismaticPowerResidueIdeal_pow (p : A) d n⟩

/-- 概要：G10で得た実冪剰余の非零次数ホモロジー消滅。
方針：標準冪零還元の離散・忠実平坦性から G10 を適用し、実合成商比較で標準 mod p 商へ移す。
規約：正の冪 n、有限正次数モニック族、p と d の個別の正則性、δ(d) の単元性を仮定する。
使われ方：BS Rem 7.15（著者版 p.62）の生成元冪商への G9 適用の入力。 -/
theorem monicPrismaticSourcePowerResidue_homology_isZero (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat Qₙ) i).obj (Y₀).obj) := by
  obtain ⟨hGE, hLE, _⟩ :=
    monicPrismaticSourcePowerResidue_pure_flat D d f n hn hf hdeg s hpA hd v hv
  rcases lt_or_gt_of_ne hi with h | h
  · exact (DerivedCategory.isGE_iff _ _).mp hGE i h
  · exact (DerivedCategory.isLE_iff _ _).mp hLE i h

/-- 概要：同じ実冪剰余のH0平坦性。
方針：標準冪零還元の離散・忠実平坦性から G10 を適用し、実合成商比較で標準 mod p 商へ移す。
規約：正の冪 n、有限正次数モニック族、p と d の個別の正則性、δ(d) の単元性を仮定する。
使われ方：BS Rem 7.15（著者版 p.62）の生成元冪商への G9 適用の入力。 -/
theorem monicPrismaticSourcePowerResidueH0_flat :
    Module.Flat Qₙ ((DerivedCategory.homologyFunctor (ModuleCat Qₙ) 0).obj (Y₀).obj) :=
  (monicPrismaticSourcePowerResidue_pure_flat D d f n hn hf hdeg s hpA hd v hv).2.2

/-- 概要：A/(dⁿ)上の標準mod p実還元の非零次数ホモロジー消滅。
方針：標準冪零還元の離散・忠実平坦性から G10 を適用し、実合成商比較で標準 mod p 商へ移す。
規約：正の冪 n、有限正次数モニック族、p と d の個別の正則性、δ(d) の単元性を仮定する。
使われ方：BS Rem 7.15（著者版 p.62）の生成元冪商への G9 適用の入力。 -/
theorem monicPrismaticSourceGeneratorPowerModP_homology_isZero (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat Mₙ) i).obj (Wₙ).obj) :=
  prismaticGeneratorPowerModP_homology_isZero p d n X₀ i
    (monicPrismaticSourcePowerResidue_homology_isZero D d f n hn hf hdeg s hpA hd v hv i hi)

/-- 概要：標準mod p実還元のH0は、その正確な商環上で平坦。
方針：標準冪零還元の離散・忠実平坦性から G10 を適用し、実合成商比較で標準 mod p 商へ移す。
規約：正の冪 n、有限正次数モニック族、p と d の個別の正則性、δ(d) の単元性を仮定する。
使われ方：BS Rem 7.15（著者版 p.62）の生成元冪商への G9 適用の入力。 -/
theorem monicPrismaticSourceGeneratorPowerModPH0_flat :
    Module.Flat Mₙ ((DerivedCategory.homologyFunctor (ModuleCat Mₙ) 0).obj (Wₙ).obj) :=
  prismaticGeneratorPowerModPH0_flat p d n X₀
    (monicPrismaticSourcePowerResidueH0_flat D d f n hn hf hdeg s hpA hd v hv)

/-- 概要：G8の商上完備性とG10の実mod p入力を、G9用の同じ対象で束ねる。
方針：標準冪零還元の離散・忠実平坦性から G10 を適用し、実合成商比較で標準 mod p 商へ移す。
規約：正の冪 n、有限正次数モニック族、p と d の個別の正則性、δ(d) の単元性を仮定する。
使われ方：BS Rem 7.15（著者版 p.62）の生成元冪商への G9 適用の入力。 -/
theorem monicPrismaticSourceGeneratorPower_G9_inputs :
    DerivedCompletion.IsComplete Tₙ (p : Tₙ) (Zₙ).obj ∧
      (∀ i : ℤ, i ≠ 0 →
        IsZero ((DerivedCategory.homologyFunctor (ModuleCat Mₙ) i).obj (Wₙ).obj)) ∧
      Module.Flat Mₙ ((DerivedCategory.homologyFunctor (ModuleCat Mₙ) 0).obj (Wₙ).obj) := by
  exact ⟨monicPrismaticSourceGeneratorPowerReduction_isComplete_over_quotient D d f hd n,
    monicPrismaticSourceGeneratorPowerModP_homology_isZero D d f n hn hf hdeg s hpA hd v hv,
    monicPrismaticSourceGeneratorPowerModPH0_flat D d f n hn hf hdeg s hpA hd v hv⟩

end SerrePositivity.BhattScholze.Andre
