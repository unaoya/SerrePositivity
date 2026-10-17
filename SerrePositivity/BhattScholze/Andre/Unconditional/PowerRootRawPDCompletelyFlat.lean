module

public import SerrePositivity.BhattScholze.Andre.Unconditional.PowerRootSourcePurity
public import SerrePositivity.BhattScholze.Andre.Unconditional.PowerRootRawPDComparison
public import SerrePositivity.CommutativeAlgebra.CompletelyFlatCriterion

/-!
# André E1・E2：有限モニック族の raw 実 PD 環の完全忠実平坦性

## 概要

完全 prism 上の正次数モニック無限根族の raw f/d 包の実 PD 完備化環は、元の (p,d) に関して
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
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect) (f : Polynomial A)
variable (hf : f.Monic) (hdeg : 0 < f.natDegree)
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "P" => PowerRootPolynomial A p hp
local notation "d" => W.generator
local notation "dP" => algebraMap A P d
local notation "E" => powerRootPolynomialDelta p hW.p_mul_injective W.deltaStructure
local notation "r" => powerRootPrismMonicUnaryFamily (p := p) f
local notation "Raw" => DeltaAdjoinDivision E dP r
local notation "c" => algebraMap A Raw
local notation "B" => PDCompletionH0 Raw p (c d)
local notation "M" => CategoryTheory.Functor.obj (ModuleCat.restrictScalars c) (ModuleCat.of Raw B)
local notation "I" => Ideal.span {(p : A), d}
local notation "Q" => A ⧸ I
local notation "q" => Ideal.Quotient.mk I
local notation "X" => PowerRootPrismMonicSourceIteratedPDCompletion_of_unconditional W hW f
local notation "Y" => CategoryTheory.Functor.obj (boundedAboveDerivedBaseChange q)
  (boundedAboveDerivedSingleFunctor.obj M)
include hf hdeg

/-- 概要：元の実逐次源は、標準A作用付きraw PD環のsingle対象と同型。
方針：実完備化源の純性と同じ A 線形 H⁰ 比較を用い、実剰余の離散・忠実平坦性を移す。
規約：完全 prism とモニック性、正次数を仮定し、元の係数作用を固定する。
使われ方：BS Rem 7.15（著者版 p.62）の最終完全 prism 候補との比較への入力。 -/
def powerRootPrismMonicSourcePDSingleIso_of_unconditional : X ≅ boundedAboveDerivedSingleFunctor.obj M :=
  ObjectProperty.isoMk _ (powerRootPrismMonicSourceSingleIso_of_unconditional W hW f hf hdeg ≪≫
    (DerivedCategory.singleFunctor (ModuleCat A) 0).mapIso (powerRootPrismMonicSourcePDH0Iso_of_unconditional W hW f))

/-- 概要：実PD環の同じ(p,d)導来還元の非零次数は消える。
方針：実完備化源の純性と同じ A 線形 H⁰ 比較を用い、実剰余の離散・忠実平坦性を移す。
規約：完全 prism とモニック性、正次数を仮定し、元の係数作用を固定する。
使われ方：BS Rem 7.15（著者版 p.62）の最終完全 prism 候補との比較への入力。 -/
theorem powerRootPrismMonicRawPD_reduction_homology_isZero_of_unconditional (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat Q) i).obj (Y).obj) := by
  have hz := powerRootPrismMonicSourceIteratedPDResidue_homology_isZero_of_unconditional W hW f hf i hi
  exact hz.of_iso ((DerivedCategory.homologyFunctor (ModuleCat Q) i).mapIso
    (DerivedCategory.Minus.ι.mapIso
      ((boundedAboveDerivedBaseChange q).mapIso
        (powerRootPrismMonicSourcePDSingleIso_of_unconditional W hW f hf hdeg)))).symm

/-- 概要：実PD環の同じ(p,d)導来還元のH0は忠実平坦。
方針：実完備化源の純性と同じ A 線形 H⁰ 比較を用い、実剰余の離散・忠実平坦性を移す。
規約：完全 prism とモニック性、正次数を仮定し、元の係数作用を固定する。
使われ方：BS Rem 7.15（著者版 p.62）の最終完全 prism 候補との比較への入力。 -/
theorem powerRootPrismMonicRawPD_reductionH0_faithfullyFlat_of_unconditional :
    Module.FaithfullyFlat Q ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj (Y).obj) := by
  let : Module.FaithfullyFlat Q
      ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj
        ((boundedAboveDerivedBaseChange q).obj X).obj) :=
    powerRootPrismMonicSourceIteratedPDResidueH0_faithfullyFlat_of_initialCoefficient W hW f
      (InitialCoefficient.sourceResidueH0_faithfullyFlat W hW f hf hdeg)
  exact Module.FaithfullyFlat.of_linearEquiv Q
    ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj
      ((boundedAboveDerivedBaseChange q).obj X).obj)
    ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).mapIso
      (DerivedCategory.Minus.ι.mapIso
        ((boundedAboveDerivedBaseChange q).mapIso
          (powerRootPrismMonicSourcePDSingleIso_of_unconditional W hW f hf hdeg)))).toLinearEquiv.symm

/-- 概要：実PD環の具体的A係数加群の(p,d)高次Torは零。
方針：実完備化源の純性と同じ A 線形 H⁰ 比較を用い、実剰余の離散・忠実平坦性を移す。
規約：完全 prism とモニック性、正次数を仮定し、元の係数作用を固定する。
使われ方：BS Rem 7.15（著者版 p.62）の最終完全 prism 候補との比較への入力。 -/
theorem powerRootPrismMonicRawPD_torVanishing_of_unconditional : scalarExtensionTorVanishing q M := by
  apply (derivedModuleBaseChange_negative_homology_vanishes_iff q M).mp
  intro n hn
  exact (powerRootPrismMonicRawPD_reduction_homology_isZero_of_unconditional W hW f hf hdeg (-(n : ℤ)) (by omega)).of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat Q) (-(n : ℤ))).mapIso
      ((boundedAboveDerivedBaseChangeModuleNatIso q).app M)).symm

/-- 概要：実PD環の通常係数拡大も同じ商環上忠実平坦。
方針：実完備化源の純性と同じ A 線形 H⁰ 比較を用い、実剰余の離散・忠実平坦性を移す。
規約：完全 prism とモニック性、正次数を仮定し、元の係数作用を固定する。
使われ方：BS Rem 7.15（著者版 p.62）の最終完全 prism 候補との比較への入力。 -/
theorem powerRootPrismMonicRawPD_scalarExtension_faithfullyFlat_of_unconditional :
    Module.FaithfullyFlat Q ((ModuleCat.extendScalars q).obj M) := by
  let : Module.FaithfullyFlat Q
      ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj (Y).obj) :=
    powerRootPrismMonicRawPD_reductionH0_faithfullyFlat_of_unconditional W hW f hf hdeg
  exact Module.FaithfullyFlat.of_linearEquiv Q
    ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj (Y).obj)
    ((boundedAboveDerivedBaseChangeModuleH0Iso q).app M).toLinearEquiv.symm

/-- 概要：正次数モニック無限根族のraw実PD環は、元の(p,d)に関して完全忠実平坦。
方針：実完備化源の純性と同じ A 線形 H⁰ 比較を用い、実剰余の離散・忠実平坦性を移す。
規約：完全 prism とモニック性、正次数を仮定し、元の係数作用を固定する。
使われ方：BS Rem 7.15（著者版 p.62）の最終完全 prism 候補との比較への入力。 -/
theorem powerRootPrismMonicRawPD_isCompletelyFaithfullyFlat_of_unconditional :
    IsCompletelyFaithfullyFlat I (ModuleCat.carrier M) := by
  let Mc : ModuleCat.{u} A := M
  have hFF : Module.FaithfullyFlat Q ((ModuleCat.extendScalars q).obj Mc) :=
    powerRootPrismMonicRawPD_scalarExtension_faithfullyFlat_of_unconditional W hW f hf hdeg
  refine ⟨isCompletelyFlat_of_acyclic_flat_reduction I Mc
    (powerRootPrismMonicRawPD_torVanishing_of_unconditional W hW f hf hdeg) hFF.1, ?_⟩
  let e := (quotientScalarExtensionEquiv I Mc).trans (quotientTensorReductionEquiv I Mc).symm
  let := hFF
  exact Module.FaithfullyFlat.of_linearEquiv _ _ e.symm

/-- 概要：元の raw PD 実完備化 H の標準分母像は正則。
方針：元の実源 H⁰ の A 線形比較で生成元の単射性を移し、標準完備化射の作用を照合する。
規約：同じ H と同じ分母像を用い、hpR を仮定しない。正次数モニック入力を要求する。
使われ方：BS Rem 7.15（著者版 p.62）の元の H の prism 構造への無条件入力。 -/
theorem powerRootPrismMonicRaw_pdCompletion_generator_regular_of_unconditional :
    let := pdCompletionCommRing Raw p (c d)
    IsSMulRegular B (pdCompletionUnit Raw p (c d) (c d)) := by
  let := pdCompletionCommRing Raw p (c d)
  let := pdCompletionAlgebra Raw p (c d)
  let e := (powerRootPrismMonicSourcePDH0Iso_of_unconditional W hW f).toLinearEquiv
  have hsrc :=
    (powerRootPrismMonicSourceIteratedPDCompletion_pure_regular_of_unconditional
      W hW f hf hdeg).2.2
  have hM : Function.Injective (fun x : ModuleCat.carrier M => d • x) := by
    intro x y hxy
    apply e.symm.injective
    apply hsrc
    simpa only [← e.symm.map_smul] using congrArg e.symm hxy
  change Function.Injective (fun x : B => pdCompletionUnit Raw p (c d) (c d) * x)
  intro x y hxy
  apply hM
  change (c d) • (x : B) = (c d) • (y : B)
  have hmap : algebraMap Raw B (c d) = pdCompletionUnit Raw p (c d) (c d) :=
    pairCompletion_algebraMap Raw (p : Raw) (c d) (c d)
  simpa only [Algebra.smul_def, hmap] using hxy

end SerrePositivity.BhattScholze.Andre
