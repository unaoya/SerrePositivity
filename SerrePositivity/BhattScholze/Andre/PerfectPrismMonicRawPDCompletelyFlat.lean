module

public import SerrePositivity.BhattScholze.Andre.PerfectPrismMonicSourceDiscrete
public import SerrePositivity.BhattScholze.Andre.MonicPrismaticRawPDComparison
public import SerrePositivity.CommutativeAlgebra.CompletelyFlatCriterion

/-!
# André E1・E2：有限モニック族の raw 実 PD 環の完全忠実平坦性

## 概要

完全 prism 上の有限正次数モニック族の raw f/d 包の実 PD 完備化環は、元の (p,d) に関して
完全忠実平坦。BS Rem 7.15（著者版 p.62）の環候補への平坦性の移送。

## 方針

同じ実源の離散性と、元の係数作用を保つ H⁰ 比較から raw PD 環の single 比較を構成する。
実剰余の Tor 消滅と忠実平坦性を完全忠実平坦性の一般判定へ渡す。
原典の Prop 7.11 を用いる証明とは異なる経路の計算。

## 規約

この raw PD 環の完全 δ 化と最終 perfectoid 商への比較は別工程。

## 使われ方

完全 δ 化と実完備化の既存比較を介して、最終根付き perfectoid 候補の平坦性へ進む。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.DerivedCompletion
open scoped TensorProduct
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (P : OrientedPrism p A) (hP : P.deltaStructure.IsPerfect) (f : σ → Polynomial A)
variable (hf : ∀ t, (f t).Monic) (hdeg : ∀ t, 0 < (f t).natDegree)
variable {m : ℕ} (s : Fin m ≃ σ)
local notation "D" => OrientedPrism.deltaStructure P
local notation "d" => OrientedPrism.generator P
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "r" => (fun t : σ => monicRelation (f t) t)
local notation "Raw" => DeltaAdjoinDivision E (MvPolynomial.C d) r
local notation "c" => algebraMap A Raw
local notation "B" => PDCompletionH0 Raw p (c d)
local notation "M" => CategoryTheory.Functor.obj (ModuleCat.restrictScalars c) (ModuleCat.of Raw B)
local notation "I" => Ideal.span {(p : A), d}
local notation "Q" => A ⧸ I
local notation "q" => Ideal.Quotient.mk I
local notation "X" => MonicPrismaticSourceIteratedPDCompletion D d f
local notation "Y" => CategoryTheory.Functor.obj (boundedAboveDerivedBaseChange q)
  (boundedAboveDerivedSingleFunctor.obj M)
include hP hf hdeg s

/-- 概要：元の実逐次源は、標準A作用付きraw PD環のsingle対象と同型。
方針：実完備化源の純性と同じ A 線形 H⁰ 比較を用い、実剰余の離散・忠実平坦性を移す。
規約：完全 prism と有限全列挙、モニック性、正次数を仮定し、元の係数作用を固定する。
使われ方：BS Rem 7.15（著者版 p.62）の最終完全 prism 候補との比較への入力。 -/
def perfectPrismMonicSourcePDSingleIso : X ≅ boundedAboveDerivedSingleFunctor.obj M :=
  ObjectProperty.isoMk _ (perfectPrismMonicSourceSingleIso P hP f hf hdeg s ≪≫
    (DerivedCategory.singleFunctor (ModuleCat A) 0).mapIso (monicPrismaticSourcePDH0Iso D d f))

/-- 概要：実PD環の同じ(p,d)導来還元の非零次数は消える。
方針：実完備化源の純性と同じ A 線形 H⁰ 比較を用い、実剰余の離散・忠実平坦性を移す。
規約：完全 prism と有限全列挙、モニック性、正次数を仮定し、元の係数作用を固定する。
使われ方：BS Rem 7.15（著者版 p.62）の最終完全 prism 候補との比較への入力。 -/
theorem perfectPrismMonicRawPD_reduction_homology_isZero (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat Q) i).obj (Y).obj) := by
  obtain ⟨v, hv⟩ := P.isDistinguished_of_perfect hP
  have hz := monicPrismaticSourceIteratedPDResidue_homology_isZero D d f s hf
    hP.p_mul_injective P.generator_regular v hv i hi
  exact hz.of_iso ((DerivedCategory.homologyFunctor (ModuleCat Q) i).mapIso
    (DerivedCategory.Minus.ι.mapIso
      ((boundedAboveDerivedBaseChange q).mapIso
        (perfectPrismMonicSourcePDSingleIso P hP f hf hdeg s)))).symm

/-- 概要：実PD環の同じ(p,d)導来還元のH0は忠実平坦。
方針：実完備化源の純性と同じ A 線形 H⁰ 比較を用い、実剰余の離散・忠実平坦性を移す。
規約：完全 prism と有限全列挙、モニック性、正次数を仮定し、元の係数作用を固定する。
使われ方：BS Rem 7.15（著者版 p.62）の最終完全 prism 候補との比較への入力。 -/
theorem perfectPrismMonicRawPD_reductionH0_faithfullyFlat :
    Module.FaithfullyFlat Q ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj (Y).obj) := by
  obtain ⟨v, hv⟩ := P.isDistinguished_of_perfect hP
  let : Module.FaithfullyFlat Q
      ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj
        ((boundedAboveDerivedBaseChange q).obj X).obj) :=
    monicPrismaticSourceIteratedPDResidueH0_faithfullyFlat D d f s hf hdeg
    hP.p_mul_injective P.generator_regular v hv
  exact Module.FaithfullyFlat.of_linearEquiv Q
    ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj
      ((boundedAboveDerivedBaseChange q).obj X).obj)
    ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).mapIso
      (DerivedCategory.Minus.ι.mapIso
        ((boundedAboveDerivedBaseChange q).mapIso
          (perfectPrismMonicSourcePDSingleIso P hP f hf hdeg s)))).toLinearEquiv.symm

/-- 概要：実PD環の具体的A係数加群の(p,d)高次Torは零。
方針：実完備化源の純性と同じ A 線形 H⁰ 比較を用い、実剰余の離散・忠実平坦性を移す。
規約：完全 prism と有限全列挙、モニック性、正次数を仮定し、元の係数作用を固定する。
使われ方：BS Rem 7.15（著者版 p.62）の最終完全 prism 候補との比較への入力。 -/
theorem perfectPrismMonicRawPD_torVanishing : scalarExtensionTorVanishing q M := by
  apply (derivedModuleBaseChange_negative_homology_vanishes_iff q M).mp
  intro n hn
  exact (perfectPrismMonicRawPD_reduction_homology_isZero P hP f hf hdeg s (-(n : ℤ)) (by omega)).of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat Q) (-(n : ℤ))).mapIso
      ((boundedAboveDerivedBaseChangeModuleNatIso q).app M)).symm

/-- 概要：実PD環の通常係数拡大も同じ商環上忠実平坦。
方針：実完備化源の純性と同じ A 線形 H⁰ 比較を用い、実剰余の離散・忠実平坦性を移す。
規約：完全 prism と有限全列挙、モニック性、正次数を仮定し、元の係数作用を固定する。
使われ方：BS Rem 7.15（著者版 p.62）の最終完全 prism 候補との比較への入力。 -/
theorem perfectPrismMonicRawPD_scalarExtension_faithfullyFlat :
    Module.FaithfullyFlat Q ((ModuleCat.extendScalars q).obj M) := by
  let : Module.FaithfullyFlat Q
      ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj (Y).obj) :=
    perfectPrismMonicRawPD_reductionH0_faithfullyFlat P hP f hf hdeg s
  exact Module.FaithfullyFlat.of_linearEquiv Q
    ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj (Y).obj)
    ((boundedAboveDerivedBaseChangeModuleH0Iso q).app M).toLinearEquiv.symm

/-- 概要：有限正次数モニック族のraw実PD環は、元の(p,d)に関して完全忠実平坦。
方針：実完備化源の純性と同じ A 線形 H⁰ 比較を用い、実剰余の離散・忠実平坦性を移す。
規約：完全 prism と有限全列挙、モニック性、正次数を仮定し、元の係数作用を固定する。
使われ方：BS Rem 7.15（著者版 p.62）の最終完全 prism 候補との比較への入力。 -/
theorem perfectPrismMonicRawPD_isCompletelyFaithfullyFlat :
    IsCompletelyFaithfullyFlat I (ModuleCat.carrier M) := by
  let Mc : ModuleCat.{u} A := M
  have hFF : Module.FaithfullyFlat Q ((ModuleCat.extendScalars q).obj Mc) :=
    perfectPrismMonicRawPD_scalarExtension_faithfullyFlat P hP f hf hdeg s
  refine ⟨isCompletelyFlat_of_acyclic_flat_reduction I Mc
    (perfectPrismMonicRawPD_torVanishing P hP f hf hdeg s) hFF.1, ?_⟩
  let e := (quotientScalarExtensionEquiv I Mc).trans (quotientTensorReductionEquiv I Mc).symm
  let := hFF
  exact Module.FaithfullyFlat.of_linearEquiv _ _ e.symm

end SerrePositivity.BhattScholze.Andre
