module

public import SerrePositivity.BhattScholze.Prism.Residue.PerfectDeltaPrismaticResidue
public import SerrePositivity.BhattScholze.Prism.Residue.PrismaticPowerDerivedFlat
public import SerrePositivity.BhattScholze.Andre.RootedExtension.PerfectPrismRootFamilySourceInputs

/-! # 実Frobenius係数剰余へのprism冪剰余判定の接続 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (n : ℕ)
variable (X : DerivedCategory.Minus (ModuleCat.{u} A))
local notation "Q₀" => A ⧸ Ideal.span {(p : A), d}
local notation "Jₙ" => Ideal.span {(p : A), (D.frobeniusLift ^ n) d}
local notation "Qₙ" => A ⧸ Jₙ
local notation "Y₀" => CategoryTheory.Functor.obj
  (boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {(p : A), d}))) X
local notation "Yₙ" => CategoryTheory.Functor.obj
  (boundedAboveDerivedBaseChange (Ideal.Quotient.mk Jₙ)) X

/-- 元の実還元の次数零集中・忠実平坦性を、Frobeniusで動かした係数剰余へ渡す。 -/
theorem frobeniusPrismaticDerivedReduction_pure_faithfullyFlat
    (hzero : ∀ i : ℤ, i ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat Q₀) i).obj (Y₀).obj))
    (hFF : Module.FaithfullyFlat Q₀
      ((DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj (Y₀).obj)) :
    (Yₙ).obj.IsGE 0 ∧ (Yₙ).obj.IsLE 0 ∧
      Module.FaithfullyFlat Qₙ
        ((DerivedCategory.homologyFunctor (ModuleCat Qₙ) 0).obj (Yₙ).obj) := by
  let P (J : Ideal A) : Prop :=
    let Y := (boundedAboveDerivedBaseChange (Ideal.Quotient.mk J)).obj X
    Y.obj.IsGE 0 ∧ Y.obj.IsLE 0 ∧ Module.FaithfullyFlat (A ⧸ J)
      ((DerivedCategory.homologyFunctor (ModuleCat (A ⧸ J)) 0).obj Y.obj)
  have hpow : P (Ideal.span {(p : A), d ^ (p ^ n)}) :=
    prismaticPowerDerivedReduction_pure_faithfullyFlat (p : A) d (p ^ n)
      (pow_pos (Fact.out : Nat.Prime p).pos n) X hzero hFF
  exact Eq.mp (congrArg P (frobeniusPrismaticResidueIdeal_eq D d n).symm) hpow

/-- 完全基底では、実φⁿの商係数作用で元のA/(p,d)へ制限したH0も忠実平坦。 -/
theorem perfectDeltaFrobeniusResidueH0_faithfullyFlat (hD : D.IsPerfect)
    (hzero : ∀ i : ℤ, i ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat Q₀) i).obj (Y₀).obj))
    (hFF : Module.FaithfullyFlat Q₀
      ((DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj (Y₀).obj)) :
    Module.FaithfullyFlat Q₀
      ((ModuleCat.restrictScalars
        (perfectDeltaFrobeniusPrismaticResidueEquiv D hD d n).toRingHom).obj
          ((DerivedCategory.homologyFunctor (ModuleCat Qₙ) 0).obj (Yₙ).obj)) := by
  let e := perfectDeltaFrobeniusPrismaticResidueEquiv D hD d n
  let M := (DerivedCategory.homologyFunctor (ModuleCat Qₙ) 0).obj (Yₙ).obj
  let := e.toRingHom.toAlgebra
  let : Module Q₀ M := Module.compHom M e.toRingHom
  let : IsScalarTower Q₀ Qₙ M := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let eA : Q₀ ≃ₐ[Q₀] Qₙ := AlgEquiv.ofBijective (Algebra.ofId Q₀ Qₙ) e.bijective
  have : Module.FaithfullyFlat Q₀ Qₙ :=
    Module.FaithfullyFlat.of_linearEquiv Q₀ Q₀ eA.symm.toLinearEquiv
  have : Module.FaithfullyFlat Qₙ M :=
    (frobeniusPrismaticDerivedReduction_pure_faithfullyFlat D d n X hzero hFF).2.2
  exact Module.FaithfullyFlat.trans Q₀ Qₙ M

/-- 完全prismの有限根族の実逐次源に対する、実Frobenius係数剰余の具体的入力。 -/
theorem perfectPrismRootFamilySource_frobenius_residue_inputs
    {σ : Type u} (P : OrientedPrism p A) (hP : P.deltaStructure.IsPerfect)
    (b : σ → A) {m : ℕ} (s : Fin m ≃ σ) (k : ℕ) :
    let D₀ := P.deltaStructure
    let d₀ := P.generator
    let X₀ := DeltaRootSourceIteratedPDCompletion D₀ d₀ b
    let Q := A ⧸ Ideal.span {(p : A), (D₀.frobeniusLift ^ k) d₀}
    let Y := (boundedAboveDerivedBaseChange
      (Ideal.Quotient.mk (Ideal.span {(p : A), (D₀.frobeniusLift ^ k) d₀}))).obj X₀
    (Y.obj.IsGE 0 ∧ Y.obj.IsLE 0 ∧ Module.FaithfullyFlat Q
      ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj Y.obj)) ∧
      Module.FaithfullyFlat (A ⧸ Ideal.span {(p : A), d₀})
        ((ModuleCat.restrictScalars
          (perfectDeltaFrobeniusPrismaticResidueEquiv D₀ hP d₀ k).toRingHom).obj
            ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj Y.obj)) := by
  let X₀ := DeltaRootSourceIteratedPDCompletion P.deltaStructure P.generator b
  have hz := perfectPrismRootFamilySource_modPD_homology_isZero P hP b s
  have hf := perfectPrismRootFamilySource_modPDH0_faithfullyFlat P hP b s
  exact ⟨frobeniusPrismaticDerivedReduction_pure_faithfullyFlat
      P.deltaStructure P.generator k X₀ hz hf,
    perfectDeltaFrobeniusResidueH0_faithfullyFlat P.deltaStructure P.generator k X₀ hP hz hf⟩

end SerrePositivity.BhattScholze
