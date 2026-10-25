module

public import SerrePositivity.BhattScholze.Semiperfectoid.RootEnvelope.PerfectPrismRootPerfectoidCompletelyFlat
public import SerrePositivity.BhattScholze.Semiperfectoid.RootEnvelope.RootedFamilyPerfectoidSurjectivityDescent

/-! # 完全prism商の根付きp完全忠実平坦perfectoid拡大と全射性 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (P : OrientedPrism p A) (hP : P.deltaStructure.IsPerfect)
local notation "D" => OrientedPrism.deltaStructure P
local notation "d" => OrientedPrism.generator P
local notation "hd" => OrientedPrism.isDistinguished_of_perfect P hP
local notation "R" => A ⧸ Ideal.span {d}
include hP

/-- 候補商の通常の基底代数作用も、元の標準射に関してp完全忠実平坦。 -/
theorem perfectPrismRootPerfectoid_baseAlgebra_isCompletelyFaithfullyFlat (b : σ → A) :
    letI := deltaRootPrismCommRing D d b
    letI := (deltaRootPerfectoidCandidateBaseMap D d b hd).toAlgebra
    IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) (DeltaRootPerfectoidCandidate D d b hd) := by
  let := deltaRootPrismCommRing D d b
  let T := DeltaRootPerfectoidCandidate D d b hd
  let g := deltaRootPerfectoidCandidateBaseMap D d b hd
  let := g.toAlgebra
  let I := Ideal.span {(p : R)}
  let q := Ideal.Quotient.mk I
  let M0 : ModuleCat.{u} R := baseChangeScalarModule g
  let M1 := ModuleCat.of R T
  let e : M0 ≅ M1 := algebraSelfRestrictionIso R T
  have ht : scalarExtensionTorVanishing q M1 := scalarExtensionTorVanishing_of_iso q e
    (perfectPrismRootPerfectoid_torVanishing P hP b)
  let : Module.FaithfullyFlat (R ⧸ I) ((ModuleCat.extendScalars q).obj M0) :=
    perfectPrismRootPerfectoid_scalarExtension_faithfullyFlat P hP b
  have hf : Module.FaithfullyFlat (R ⧸ I) ((ModuleCat.extendScalars q).obj M1) :=
    Module.FaithfullyFlat.of_linearEquiv (R ⧸ I) ((ModuleCat.extendScalars q).obj M0)
      (((ModuleCat.extendScalars q).mapIso e).toLinearEquiv.symm)
  refine ⟨isCompletelyFlat_of_acyclic_flat_reduction I T ht hf.1, ?_⟩
  let eTensor := (quotientScalarExtensionEquiv I M1).trans (quotientTensorReductionEquiv I T).symm
  let := hf
  exact Module.FaithfullyFlat.of_linearEquiv _ _ eTensor.symm

/-- 完全prism商の任意の元族に、具体的なp完全忠実平坦perfectoid拡大と互換根を供給する。 -/
theorem exists_rootedPerfectoidExtension_of_perfectPrism (a : σ → R) :
    ∃ (T : Type u) (_ : CommRing T) (f : R →+* T) (ρ : σ → ℕ → T),
      IsIntegralPerfectoid T p ∧
      (letI := f.toAlgebra; IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) T) ∧
      (∀ s, ρ s 0 = f (a s)) ∧ (∀ s n, ρ s (n + 1) ^ p = ρ s n) := by
  let b : σ → A := fun s => Classical.choose (Ideal.Quotient.mk_surjective (a s))
  have hb (s : σ) : Ideal.Quotient.mk (Ideal.span {d}) (b s) = a s :=
    Classical.choose_spec (Ideal.Quotient.mk_surjective (a s))
  let := deltaRootPrismCommRing D d b
  refine ⟨DeltaRootPerfectoidCandidate D d b hd, inferInstance,
    deltaRootPerfectoidCandidateBaseMap D d b hd,
    deltaRootPerfectoidCandidateRoots D d b hd,
    deltaRootPerfectoidCandidate_isIntegralPerfectoid D d b hd,
    perfectPrismRootPerfectoid_baseAlgebra_isCompletelyFaithfullyFlat P hP b, ?_, ?_⟩
  · intro s
    rw [deltaRootPerfectoidCandidateRoots_zero, hb]
  · exact deltaRootPerfectoidCandidateRoots_pow D d b hd

/-- 完全prism商の導来p完備な全射商では、任意の普遍perfectoid化は全射。 -/
theorem surjective_of_isPerfectoidization_of_perfectPrism_quotient
    {S C : Type u} [CommRing S] [CommRing C]
    (q : R →+* S) (hq : Function.Surjective q)
    (hS : DerivedCompletion.IsModuleComplete S (p : S) (ModuleCat.of S S))
    (f : S →+* C) (hf : IsPerfectoidization p f) : Function.Surjective f := by
  obtain ⟨T, hT, g, ρ, hperf, hflat, hρ0, hρ⟩ :=
    exists_rootedPerfectoidExtension_of_perfectPrism P hP (fun s : RingHom.ker q => (s : R))
  let := hT
  let := g.toAlgebra
  have hR : IsIntegralPerfectoid R p := P.quotient_isIntegralPerfectoid hP
  exact surjective_of_isPerfectoidization_of_sourceKernelRoots
    hR hperf q hq hS hflat ρ hρ0 hρ f hf

end SerrePositivity.BhattScholze
