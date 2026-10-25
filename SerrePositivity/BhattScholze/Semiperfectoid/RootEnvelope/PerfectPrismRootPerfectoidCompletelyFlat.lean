module

public import SerrePositivity.BhattScholze.Semiperfectoid.RootEnvelope.PerfectPrismRootQuotientReduction
public import SerrePositivity.BhattScholze.Prism.Residue.PrismaticGeneratorPowerModPFaithful

/-! # 任意根族のperfectoid候補の標準基底射のp完全忠実平坦性 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (P : OrientedPrism p A) (hP : P.deltaStructure.IsPerfect) (b : σ → A)
local notation "D" => OrientedPrism.deltaStructure P
local notation "d" => OrientedPrism.generator P
local notation "hd" => OrientedPrism.isDistinguished_of_perfect P hP
local notation "f" => deltaRootPrismCoefficientMap D d b
local notation "M" => baseChangeScalarModule f
local notation "X" => CategoryTheory.Functor.obj boundedAboveDerivedSingleFunctor M
local notation "J" => Ideal.span {d}
local notation "R" => A ⧸ J
local notation "q" => Ideal.Quotient.mk J
local notation "I" => Ideal.span {(p : A), d}
local notation "Q" => A ⧸ I
local notation "q₀" => Ideal.Quotient.mk I
local notation "g" => deltaRootPerfectoidCandidateBaseMap D d b hd
local notation "N" => baseChangeScalarModule g
local notation "K" => Ideal.span {(p : R)}
local notation "Qp" => R ⧸ K
local notation "qp" => Ideal.Quotient.mk K
local notation "Y" => CategoryTheory.Functor.obj (boundedAboveDerivedBaseChange qp)
  (Functor.obj boundedAboveDerivedSingleFunctor N)
include hP

/-- 既存根prismの同じ(p,d)実還元の非零次数は消える。 -/
theorem perfectPrismRootPrism_pair_homology_isZero (i : ℤ) (hi : i ≠ 0) :
    letI := deltaRootPrismCommRing D d b
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat Q) i).obj
      ((boundedAboveDerivedBaseChange q₀).obj X).obj) := by
  let := deltaRootPrismCommRing D d b
  let e := boundedAboveDerivedBaseChangeModuleAugmentationIso q₀ M
    (perfectPrismRootPrism_torVanishing P hP b)
  exact (derivedSingleHomology_isZero ((ModuleCat.extendScalars q₀).obj M) i hi).of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat Q) i).mapIso
      (DerivedCategory.Minus.ι.mapIso e))

/-- 同じ根prismの実(p,d)還元のH0は忠実平坦。 -/
theorem perfectPrismRootPrism_pairH0_faithfullyFlat :
    letI := deltaRootPrismCommRing D d b
    Module.FaithfullyFlat Q ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj
      ((boundedAboveDerivedBaseChange q₀).obj X).obj) := by
  let := deltaRootPrismCommRing D d b
  let : Module.FaithfullyFlat Q ((ModuleCat.extendScalars q₀).obj M) :=
    perfectPrismRootPrism_scalarExtension_faithfullyFlat P hP b
  exact Module.FaithfullyFlat.of_linearEquiv Q ((ModuleCat.extendScalars q₀).obj M)
    ((boundedAboveDerivedBaseChangeModuleH0Iso q₀).app M).toLinearEquiv

/-- perfectoid商の標準基底射の実mod p還元の非零次数は消える。 -/
theorem perfectPrismRootPerfectoid_modP_homology_isZero (i : ℤ) (hi : i ≠ 0) :
    letI := deltaRootPrismCommRing D d b
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat Qp) i).obj (Y).obj) := by
  let := deltaRootPrismCommRing D d b
  have hz : IsZero ((DerivedCategory.homologyFunctor (ModuleCat Qp) i).obj
      ((boundedAboveDerivedBaseChange qp).obj ((boundedAboveDerivedBaseChange q).obj X)).obj) := by
    let HQ (a : A) := IsZero ((DerivedCategory.homologyFunctor
      (ModuleCat (A ⧸ Ideal.span {(p : A), a})) i).obj
        ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {(p : A), a}))).obj X).obj)
    have hq0 : HQ d := perfectPrismRootPrism_pair_homology_isZero P hP b i hi
    have hq1 : HQ (d ^ 1) := Eq.mp (congrArg HQ (_root_.pow_one d).symm) hq0
    let HW (a : A) := IsZero ((DerivedCategory.homologyFunctor
      (ModuleCat ((A ⧸ Ideal.span {a}) ⧸ Ideal.span {(p : A ⧸ Ideal.span {a})})) i).obj
        ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk
          (Ideal.span {(p : A ⧸ Ideal.span {a})}))).obj
            ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {a}))).obj X)).obj)
    have hw1 : HW (d ^ 1) := prismaticGeneratorPowerModP_homology_isZero p d 1 X i hq1
    exact Eq.mp (congrArg HW (_root_.pow_one d)) hw1
  exact hz.of_iso ((DerivedCategory.homologyFunctor (ModuleCat Qp) i).mapIso
    (DerivedCategory.Minus.ι.mapIso ((boundedAboveDerivedBaseChange qp).mapIso
      (perfectPrismRootPrism_derivedQuotientIso P hP b)))).symm

/-- 同じ実mod p還元のH0は、正確な基底剰余環上で忠実平坦。 -/
theorem perfectPrismRootPerfectoid_modPH0_faithfullyFlat :
    letI := deltaRootPrismCommRing D d b
    Module.FaithfullyFlat Qp ((DerivedCategory.homologyFunctor (ModuleCat Qp) 0).obj (Y).obj) := by
  let := deltaRootPrismCommRing D d b
  let W := (boundedAboveDerivedBaseChange qp).obj ((boundedAboveDerivedBaseChange q).obj X)
  let : Module.FaithfullyFlat Qp
      ((DerivedCategory.homologyFunctor (ModuleCat Qp) 0).obj W.obj) := by
    let HQ (a : A) := Module.FaithfullyFlat (A ⧸ Ideal.span {(p : A), a})
      ((DerivedCategory.homologyFunctor (ModuleCat (A ⧸ Ideal.span {(p : A), a})) 0).obj
        ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {(p : A), a}))).obj X).obj)
    have hq0 : HQ d := perfectPrismRootPrism_pairH0_faithfullyFlat P hP b
    have hq1 : HQ (d ^ 1) := Eq.mp (congrArg HQ (_root_.pow_one d).symm) hq0
    let HW (a : A) := Module.FaithfullyFlat
      ((A ⧸ Ideal.span {a}) ⧸ Ideal.span {(p : A ⧸ Ideal.span {a})})
      ((DerivedCategory.homologyFunctor
        (ModuleCat ((A ⧸ Ideal.span {a}) ⧸ Ideal.span {(p : A ⧸ Ideal.span {a})})) 0).obj
        ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk
          (Ideal.span {(p : A ⧸ Ideal.span {a})}))).obj
            ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {a}))).obj X)).obj)
    have hw1 : HW (d ^ 1) := prismaticGeneratorPowerModPH0_faithfullyFlat p d 1 X hq1
    exact Eq.mp (congrArg HW (_root_.pow_one d)) hw1
  exact Module.FaithfullyFlat.of_linearEquiv Qp
    ((DerivedCategory.homologyFunctor (ModuleCat Qp) 0).obj W.obj)
    ((DerivedCategory.homologyFunctor (ModuleCat Qp) 0).mapIso
      (DerivedCategory.Minus.ι.mapIso ((boundedAboveDerivedBaseChange qp).mapIso
        (perfectPrismRootPrism_derivedQuotientIso P hP b)))).toLinearEquiv.symm

/-- 同じperfectoid商の基底係数加群の高次mod p Torは零。 -/
theorem perfectPrismRootPerfectoid_torVanishing :
    letI := deltaRootPrismCommRing D d b
    scalarExtensionTorVanishing qp N := by
  let := deltaRootPrismCommRing D d b
  apply (derivedModuleBaseChange_negative_homology_vanishes_iff qp N).mp
  intro n hn
  exact (perfectPrismRootPerfectoid_modP_homology_isZero P hP b (-(n : ℤ)) (by omega)).of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat Qp) (-(n : ℤ))).mapIso
      ((boundedAboveDerivedBaseChangeModuleNatIso qp).app N)).symm

/-- 同じperfectoid商の通常mod p係数拡大は忠実平坦。 -/
theorem perfectPrismRootPerfectoid_scalarExtension_faithfullyFlat :
    letI := deltaRootPrismCommRing D d b
    Module.FaithfullyFlat Qp ((ModuleCat.extendScalars qp).obj N) := by
  let := deltaRootPrismCommRing D d b
  let : Module.FaithfullyFlat Qp
      ((DerivedCategory.homologyFunctor (ModuleCat Qp) 0).obj (Y).obj) :=
    perfectPrismRootPerfectoid_modPH0_faithfullyFlat P hP b
  exact Module.FaithfullyFlat.of_linearEquiv Qp
    ((DerivedCategory.homologyFunctor (ModuleCat Qp) 0).obj (Y).obj)
    ((boundedAboveDerivedBaseChangeModuleH0Iso qp).app N).toLinearEquiv.symm

/-- 任意根族のperfectoid候補の標準基底射はp完全忠実平坦。 -/
theorem perfectPrismRootPerfectoid_isCompletelyFaithfullyFlat :
    letI := deltaRootPrismCommRing D d b
    IsCompletelyFaithfullyFlat K (ModuleCat.carrier N) := by
  let := deltaRootPrismCommRing D d b
  let Nc : ModuleCat.{u} R := N
  have hf : Module.FaithfullyFlat Qp ((ModuleCat.extendScalars qp).obj Nc) :=
    perfectPrismRootPerfectoid_scalarExtension_faithfullyFlat P hP b
  refine ⟨isCompletelyFlat_of_acyclic_flat_reduction K Nc
    (perfectPrismRootPerfectoid_torVanishing P hP b) hf.1, ?_⟩
  let e := (quotientScalarExtensionEquiv K Nc).trans (quotientTensorReductionEquiv K Nc).symm
  let := hf
  exact Module.FaithfullyFlat.of_linearEquiv _ _ e.symm

end SerrePositivity.BhattScholze
