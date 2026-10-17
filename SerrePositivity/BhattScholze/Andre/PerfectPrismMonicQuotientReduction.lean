module

public import SerrePositivity.BhattScholze.Andre.PerfectPrismMonicPrismResidue
public import SerrePositivity.HomologicalAlgebra.AlgebraRestrictionSingle
public import SerrePositivity.HomologicalAlgebra.RegularPrincipalTor

/-!
# André E1・E2：多項式 prism 候補の実生成元商と標準 perfectoid 商

## 概要

既存多項式 prism 候補の生成元による実導来商は、標準基底射を持つ perfectoid 候補の single と同型。
BS Rem 7.15（著者版 p.62）の商の実基底変更比較。

## 方針

元と候補の生成元の正則性から Tor 消滅を得て、通常商の標準係数作用を照合する。
原典の Prop 7.11 を用いる証明とは異なる具体的係数射による計算。

## 規約

この商比較は任意多項式族に対して行い、平坦性を仮定しない。

## 使われ方

prism 側の実 (p,d) 剰余入力を、元の A/d 上の標準 mod p 商へ移す。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard adicQuotientAlgebra
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (P : OrientedPrism p A) (hP : P.deltaStructure.IsPerfect) (f : σ → Polynomial A)
local notation "D" => OrientedPrism.deltaStructure P
local notation "d" => OrientedPrism.generator P
local notation "hd" => OrientedPrism.isDistinguished_of_perfect P hP
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "r" => (fun a : σ => monicRelation (f a) a)
local notation "T" => DivisionPrismCarrier E (MvPolynomial.C d) r
local notation "φ" => polynomialPrismCoefficientMap D d f
local notation "J" => Ideal.span {d}
local notation "R" => A ⧸ J
local notation "q" => Ideal.Quotient.mk J
local notation "P'" => polynomialPrism D d f hd
local notation "S" => PolynomialPerfectoidCandidate D d f hd
local notation "g" => polynomialPerfectoidCandidateBaseMap D d f hd
local notation "M" => baseChangeScalarModule φ
include hP

/-- 概要：候補の生成元の正則性は、元Aのdによるスカラー作用の正則性でもある。
方針：候補生成元の正則性と標準係数射のイデアル像を使い、通常商比較と標準 augmentation を合成する。
規約：任意多項式族を扱い、モニック性・正次数・有限性を使わない。
使われ方：BS Rem 7.15（著者版 p.62）の perfectoid 商上の実 mod p 還元。 -/
theorem perfectPrismMonicPrism_generator_smul_regular :
    letI := polynomialPrismCommRing D d f
    IsSMulRegular (ModuleCat.carrier M) d := by
  let := polynomialPrismCommRing D d f
  intro x y h
  change T at x y
  change φ d * x = φ d * y at h
  exact (P').generator_regular h

/-- 概要：元と候補の生成元が正則なので、生成元商への実係数拡大はTor非輪状。
方針：候補生成元の正則性と標準係数射のイデアル像を使い、通常商比較と標準 augmentation を合成する。
規約：任意多項式族を扱い、モニック性・正次数・有限性を使わない。
使われ方：BS Rem 7.15（著者版 p.62）の perfectoid 商上の実 mod p 還元。 -/
theorem perfectPrismMonicPrism_generator_torVanishing :
    letI := polynomialPrismCommRing D d f
    scalarExtensionTorVanishing q M := by
  let := polynomialPrismCommRing D d f
  exact scalarExtensionTorVanishing_principal_of_regular d P.generator_regular M
    (perfectPrismMonicPrism_generator_smul_regular P hP f)

/-- 概要：通常生成元商の標準係数作用を既存perfectoid候補の基底射と照合する。
方針：候補生成元の正則性と標準係数射のイデアル像を使い、通常商比較と標準 augmentation を合成する。
規約：任意多項式族を扱い、モニック性・正次数・有限性を使わない。
使われ方：BS Rem 7.15（著者版 p.62）の perfectoid 商上の実 mod p 還元。 -/
def perfectPrismMonicPrism_ordinaryQuotientIso :
    letI := polynomialPrismCommRing D d f
    (ModuleCat.extendScalars q).obj M ≅ baseChangeScalarModule g := by
  let := polynomialPrismCommRing D d f
  let := polynomialPrismCoefficientAlgebra D d f
  have hI : (J).map (algebraMap A T) = (P').ideal := by
    change (J).map φ = (P').ideal
    exact polynomialPrismCoefficientMap_ideal D d f hd
  let eR : (T ⧸ (J).map (algebraMap A T)) ≃+* S := Ideal.quotEquivOfEq hI
  let Mc : ModuleCat.{u} R := ModuleCat.of R (T ⧸ (J).map (algebraMap A T))
  let Nc : ModuleCat.{u} R := baseChangeScalarModule g
  let eA : Mc ≃ₗ[R] Nc :=
    { eR.toAddEquiv with
      map_smul' := by
        intro a x
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
        change eR (Ideal.Quotient.mk _ (φ a) * x) =
          eR (Ideal.Quotient.mk _ (φ a)) * eR x
        exact map_mul eR _ _ }
  exact (ModuleCat.extendScalars q).mapIso (algebraSelfRestrictionIso A T) ≪≫
    (quotientAlgebraScalarExtensionEquiv J T).toModuleIso ≪≫ eA.toModuleIso

/-- 概要：元の実生成元還元は、既存perfectoid商の同じ基底射付きsingle対象と同型。
方針：候補生成元の正則性と標準係数射のイデアル像を使い、通常商比較と標準 augmentation を合成する。
規約：任意多項式族を扱い、モニック性・正次数・有限性を使わない。
使われ方：BS Rem 7.15（著者版 p.62）の perfectoid 商上の実 mod p 還元。 -/
def perfectPrismMonicPrism_derivedQuotientIso :
    letI := polynomialPrismCommRing D d f
    (boundedAboveDerivedBaseChange q).obj (boundedAboveDerivedSingleFunctor.obj M) ≅
      boundedAboveDerivedSingleFunctor.obj (baseChangeScalarModule g) := by
  let := polynomialPrismCommRing D d f
  exact boundedAboveDerivedBaseChangeModuleAugmentationIso q M
    (perfectPrismMonicPrism_generator_torVanishing P hP f) ≪≫
      boundedAboveDerivedSingleFunctor.mapIso (perfectPrismMonicPrism_ordinaryQuotientIso P hP f)

end SerrePositivity.BhattScholze.Andre
