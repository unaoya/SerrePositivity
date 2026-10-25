module

public import SerrePositivity.BhattScholze.Andre.PerfectPrismMonicPrismResidue
public import SerrePositivity.BhattScholze.Andre.Variants.ArbitraryPerfectPrismMonicPrismCompletelyFlat

/-!
# André E1・E2（任意族）：既存モニック prism 候補の標準剰余入力

## 概要

完全 prism 上の任意正次数モニック族について、既存候補の標準 (p,d) 係数拡大は高次 Tor が零で、
通常係数拡大が忠実平坦。BS Rem 7.15（著者版 p.62）の perfectoid 商への入力。

## 方針

一般 δ 代数の実 PD 完備化の同じ標準射の結果を、候補比較の A 線形同型で移す。
原典の Prop 7.11 を使う証明とは異なる具体的係数射の計算。

## 規約

元の A 作用を持つ baseChangeScalarModule を固定し、商の基底環を取り替えない。

## 使われ方

生成元商と標準 mod p 商の実導来合成比較へ渡す。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (P : OrientedPrism p A) (hP : P.deltaStructure.IsPerfect) (f : σ → Polynomial A)
variable (hf : ∀ t, (f t).Monic) (hdeg : ∀ t, 0 < (f t).natDegree)
local notation "D" => OrientedPrism.deltaStructure P
local notation "d" => OrientedPrism.generator P
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "r" => (fun a : σ => monicRelation (f a) a)
local notation "Raw" => DeltaAdjoinDivision E (MvPolynomial.C d) r
local notation "F" => deltaAdjoinDivisionStructure E (MvPolynomial.C d) r
local notation "c" => algebraMap A Raw
local notation "z" => c d
local notation "G" => deltaPDCompletionStructure F z
local notation "v" => pdCompletionUnit Raw p z
local notation "j" => RingHom.comp v c
local notation "C" => DeltaPerfection G
local notation "κ" => deltaAlgebraPerfectionCoefficient G j
local notation "t" => RingHom.comp (pdCompletionUnit C p (κ d)) κ
local notation "φ" => polynomialPrismCoefficientMap D d f
local notation "M" => baseChangeScalarModule φ
local notation "I" => Ideal.span {(p : A), d}
local notation "Q" => A ⧸ I
local notation "q" => Ideal.Quotient.mk I
include hP hf hdeg

/-- 概要：既存候補の標準係数加群は元の (p,d) 商への拡大で高次 Tor が零。
方針：PD 先行構成の標準 Tor 消滅を係数射を保つ加群同型で移す。
規約：任意正次数モニック族と完全 prism を仮定する。
使われ方：BS Rem 7.15（著者版 p.62）の perfectoid 商の実 mod p 還元。 -/
theorem perfectPrismMonicPrism_torVanishing_arbitrary :
    letI := polynomialPrismCommRing D d f
    scalarExtensionTorVanishing q M := by
  let := pdCompletionCommRing Raw p z
  let := pdCompletionCommRing C p (κ d)
  let := polynomialPrismCommRing D d f
  exact scalarExtensionTorVanishing_of_iso q (monicPrismaticPDPerfectionCandidateModuleIso D d f)
    (perfectPrismDeltaAlgebraPD_torVanishing P G j hP
      (monicPrismaticPDSourceCoefficient_isDeltaHom D d f)
      (perfectPrismMonicPDSource_reduction_homology_isZero_arbitrary P hP f hf hdeg )
      (perfectPrismMonicPDSource_reductionH0_faithfullyFlat_arbitrary P hP f hf hdeg ))

/-- 概要：既存候補の同じ標準係数加群の通常 (p,d) 係数拡大は忠実平坦。
方針：PD 先行構成の通常剰余忠実平坦性を同じ線形比較で移す。
規約：元の係数商 A/(p,d) と実係数射を固定する。
使われ方：BS Rem 7.15（著者版 p.62）の perfectoid 商上の p 完全忠実平坦性。 -/
theorem perfectPrismMonicPrism_scalarExtension_faithfullyFlat_arbitrary :
    letI := polynomialPrismCommRing D d f
    Module.FaithfullyFlat Q ((ModuleCat.extendScalars q).obj M) := by
  let := pdCompletionCommRing Raw p z
  let := pdCompletionCommRing C p (κ d)
  let := polynomialPrismCommRing D d f
  let M₀ : ModuleCat.{u} A := baseChangeScalarModule t
  let : Module.FaithfullyFlat Q ((ModuleCat.extendScalars q).obj M₀) :=
    perfectPrismDeltaAlgebraPD_scalarExtension_faithfullyFlat P G j hP
      (monicPrismaticPDSourceCoefficient_isDeltaHom D d f)
      (perfectPrismMonicPDSource_reduction_homology_isZero_arbitrary P hP f hf hdeg )
      (perfectPrismMonicPDSource_reductionH0_faithfullyFlat_arbitrary P hP f hf hdeg )
  exact Module.FaithfullyFlat.of_linearEquiv Q ((ModuleCat.extendScalars q).obj M₀)
    (((ModuleCat.extendScalars q).mapIso
      (monicPrismaticPDPerfectionCandidateModuleIso D d f)).toLinearEquiv.symm)

end SerrePositivity.BhattScholze.Andre
