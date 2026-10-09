module

public import SerrePositivity.Core.FirstComparison
public import SerrePositivity.Core.NormApplication
public import SerrePositivity.Support.Resolution
public import SerrePositivity.IntersectionMultiplicity.FiniteExtension
public import SerrePositivity.IntersectionMultiplicity.OrdinaryEvaluation

/-!
# Lemma 5.2: the first norm comparison

This proof takes the general standard input interfaces in
`Inputs/IntersectionTheory.lean` explicitly. It constructs the resolution,
checks support, instantiates Lemma 3.5 with Theorem 2.5, identifies its Euler
evaluations, and independently obtains both finite-extension rank factors.
No input is the conclusion of Lemma 5.2 or either of its comparisons.
-/

public section

universe u

open CategoryTheory IsLocalRing

namespace SerrePositivity.CoreData

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]
  [Inputs.RegularHomologicalAlgebra R] [Inputs.IntersectionAdditivity R]
  [Inputs.FiniteModuleGeometry R] [Inputs.IntersectionVanishing R]
  {P Q : Ideal R} [P.IsPrime] [Q.IsPrime] (X : CoreData R P Q)

/-- **Lemma 5.2**. The standard homological, finite-module and vanishing inputs
are explicit class arguments. The paper-specific derivation has no `sorry`.
Lemma 3.5 is used through its existing interface. -/
theorem firstComparison (p : ℕ) [Fact p.Prime] [CharP (ResidueField R) p]
    (hpaper : X.IsPaperData)
    (hsum : ringKrullDim (R ⧸ P) + ringKrullDim (R ⧸ Q) = ringKrullDim R)
    (hprimary : (P ⊔ Q).radical = maximalIdeal R) : X.FirstComparison := by
  have : Module.Finite (R ⧸ P) X.D' := hpaper.finiteD
  have : Module.Finite (R ⧸ Q) X.E' := hpaper.finiteE
  have : Module.Finite R X.D' := Module.Finite.trans (R ⧸ P) X.D'
  have : Module.Finite R X.E' := Module.Finite.trans (R ⧸ Q) X.E'
  have rankD : 0 < Module.finrank (R ⧸ P) X.D' := by
    rw [← hpaper.aD_eq]
    exact X.aD_pos
  have rankE : 0 < Module.finrank (R ⧸ Q) X.E' := by
    rw [← hpaper.aE_eq]
    exact X.aE_pos
  have dimD : ringKrullDim (R ⧸ P) = X.hD :=
    (Inputs.FiniteModuleGeometry.ringDim_of_rank_pos P X.D' rankD).symm.trans hpaper.baseD.dim
  have dimE : ringKrullDim (R ⧸ Q) = X.hE :=
    (Inputs.FiniteModuleGeometry.ringDim_of_rank_pos Q X.E' rankE).symm.trans hpaper.baseE.dim
  have dimR : ((X.hD + X.hE : ℕ) : WithBot ℕ∞) = ringKrullDim R := by
    simpa only [dimD, dimE, Nat.cast_add] using hsum
  have hRanks : chi R X.D' X.E' = (X.aD : ℤ) * X.aE * chi R (R ⧸ P) (R ⧸ Q) := by
    simpa only [hpaper.aD_eq, hpaper.aE_eq] using
      chi_finite_extensions P Q X.D' X.E' rankD rankE hprimary X.hD X.hE dimD dimE dimR
  have htensor := Inputs.FiniteModuleGeometry.tensor_finite P Q X.D' X.E'
    (quotient_action_annihilator P X.D') (quotient_action_annihilator Q X.E') hprimary
  obtain ⟨F, ⟨hF⟩, hbound, hfree, hfinite⟩ :=
    Inputs.RegularHomologicalAlgebra.resolution (R := R) X.E'
  let L := baseChange (algebraMap R X.D') F
  have hL : IsPerfectSupported (algebraMap X.AD X.D' ∘ X.tD) L :=
    isPerfectSupported_baseChange_resolution X.E' F hF hbound hfree hfinite htensor
      (algebraMap X.AD X.D' ∘ X.tD) hpaper.baseD.sop.2
  have hOrd : chiOrd L = (chi R X.D' X.E' : ℝ) :=
    chiOrd_baseChange_resolution X.E' F hF hpaper.residueD htensor
  have : IsRegularLocalRing X.AD := hpaper.baseD.regular
  have : Module.Finite X.AD X.D' := hpaper.baseD.finite
  let : Algebra X.AD X.CD :=
    ((algebraMap X.D' X.CD).comp (algebraMap X.AD X.D')).toAlgebra
  have : IsScalarTower X.AD X.D' X.CD := IsScalarTower.of_algebraMap_eq' rfl
  let eR := residueFieldEquiv_of_surjective (R := R) X.D' hpaper.residueD
  let eA := residueFieldEquiv_of_surjective (R := X.AD) X.D' hpaper.baseD.residue_surjective
  have : CharP (ResidueField X.AD) p :=
    charP_of_injective_ringHom (f := (eR.trans eA.symm).toRingHom)
      (eR.trans eA.symm).injective p
  have : FaithfulSMul X.AD X.D' :=
    (faithfulSMul_iff_algebraMap_injective X.AD X.D').mpr hpaper.baseD.injective
  have hsurj := Algebra.IsIntegral.comap_surjective X.AD X.D'
  have hnorm := normComparison_of_lengthAlgebra X.AD X.D' X.CD X.tD hpaper.baseD
    X.lamD hpaper.lengthD p X.GD hsurj hpaper.transitiveD ⟨L, hL⟩
  exact X.firstComparison_of_resolution F hF hnorm.1 hnorm.2 hOrd hRanks

end SerrePositivity.CoreData
