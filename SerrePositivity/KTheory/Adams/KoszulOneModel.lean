module

public import SerrePositivity.KTheory.Adams.CyclicTwo
public import SerrePositivity.PerfectComplex.Closure
public import SerrePositivity.PerfectComplex.K0Comparison

/-! # The one-element Koszul model and unit rescalings -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u

namespace SerrePositivity
open CategoryTheory Category Limits
variable {R : Type u} [CommRing R]

namespace Adams

abbrev oneKoszulComplex (a : R) := koszulComplex (fun _ : Fin 1 => a)
abbrev oneKoszulSupport (a : R) := supportZeroLocus (Ideal.span ({a} : Set R))

lemma oneKoszulComplex_perfect (a : R) : strictlyPerfectComplex R (oneKoszulComplex a) :=
  (isPerfectSupported_koszulComplex (fun _ : Fin 1 => a)).strictlyPerfect

lemma oneKoszulComplex_support (a : R) :
    HasHomologySupportOn (oneKoszulSupport a) (oneKoszulComplex a) := by
  have h := (isPerfectSupported_koszulComplex (fun _ : Fin 1 => a)).supported.homologySupport
  change HasHomologySupport (Ideal.span ({a} : Set R)) (oneKoszulComplex a)
  simpa only [Set.range_const] using h

abbrev oneKoszulUnit : CochainComplex (ModuleCat.{u} R) ℤ :=
  (HomologicalComplex.single (ModuleCat.{u} R) (.up ℤ) 0).obj (ModuleCat.of R R)

def oneKoszulConeIso (a : R) :
    oneKoszulComplex a ≅ CochainComplex.mappingCone (smulId a (oneKoszulUnit (R := R))) :=
  Iso.refl _

def cochainScalarUnitIso (P : CochainComplex (ModuleCat.{u} R) ℤ) (u : Rˣ) : P ≅ P where
  hom := (u : R) • 𝟙 P
  inv := ((u⁻¹ : Rˣ) : R) • 𝟙 P
  hom_inv_id := by simp [Linear.comp_smul, smul_smul]
  inv_hom_id := by simp [Linear.comp_smul, smul_smul]

/-- Multiplying the Koszul differential by a unit preserves its chain-isomorphism class. -/
def scalarConeUnitMulIso (P : CochainComplex (ModuleCat.{u} R) ℤ) (a : R) (u : Rˣ) :
    CochainComplex.mappingCone (smulId ((u : R) * a) P) ≅
      CochainComplex.mappingCone (smulId a P) :=
  HomologicalComplex.homotopyCofiber.mapArrowIso _ _ (fun j => ⟨j - 1, by simp⟩)
    (Arrow.isoMk (cochainScalarUnitIso P u) (Iso.refl P) (by
      simp [cochainScalarUnitIso, smulId, Linear.comp_smul, smul_smul, mul_comm]))

def oneKoszulUnitMulIso (a : R) (u : Rˣ) : oneKoszulComplex ((u : R) * a) ≅ oneKoszulComplex a :=
  oneKoszulConeIso _ ≪≫ scalarConeUnitMulIso (oneKoszulUnit (R := R)) a u ≪≫
    (oneKoszulConeIso a).symm

lemma oneKoszulUnitMul_support (a : R) (u : Rˣ) :
    HasHomologySupportOn (oneKoszulSupport a) (oneKoszulComplex ((u : R) * a)) :=
  (oneKoszulComplex_support a).of_iso (oneKoszulUnitMulIso a u).symm

lemma oneKoszulUnitMul_class (a : R) (u : Rˣ) :
    K0WithSupport.mk (oneKoszulSupport a)
      (supportedPerfectOnObj (oneKoszulSupport a) (oneKoszulComplex ((u : R) * a))
        (oneKoszulComplex_perfect _) (oneKoszulUnitMul_support a u)) =
    K0WithSupport.mk (oneKoszulSupport a)
      (supportedPerfectOnObj (oneKoszulSupport a) (oneKoszulComplex a)
        (oneKoszulComplex_perfect a) (oneKoszulComplex_support a)) :=
  K0WithSupport.mk_eq_of_quasiIso (oneKoszulSupport a) _ _
    (oneKoszulComplex_perfect _) (oneKoszulComplex_perfect a)
    (oneKoszulUnitMul_support a u) (oneKoszulComplex_support a) (oneKoszulUnitMulIso a u).hom

end Adams
end SerrePositivity
