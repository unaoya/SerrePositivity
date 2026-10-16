module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PowerImageTower
public import SerrePositivity.HomologicalAlgebra.ModuleTensorCochainExact
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Ordinary power cokernels in flat models compute quotient-coefficient tensor -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex
variable {R : Type u} [CommRing R] (a : R)

/-- The original R-linear quotient map, including the zeroth power quotient. -/
def powerQuotientCoefficientMap (n : ℕ) :
    ModuleCat.of R R ⟶ ModuleCat.of R (R ⧸ Ideal.span {a ^ n}) :=
  ModuleCat.ofHom (Ideal.Quotient.mkₐ R (Ideal.span {a ^ n})).toLinearMap

instance powerQuotientCoefficientMap_epi (n : ℕ) : Epi (powerQuotientCoefficientMap a n) :=
  (ModuleCat.epi_iff_surjective _).mpr Ideal.Quotient.mk_surjective

abbrev powerQuotientCoefficientShortComplex (n : ℕ) : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk (a ^ n • 𝟙 (ModuleCat.of R R)) (powerQuotientCoefficientMap a n) (by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    change Ideal.Quotient.mk (Ideal.span {a ^ n}) (a ^ n * r) = 0
    apply (Ideal.Quotient.eq_zero_iff_mem).mpr
    exact Ideal.mem_span_singleton.mpr ⟨r, rfl⟩)

lemma powerQuotientCoefficientShortComplex_exact (n : ℕ) :
    (powerQuotientCoefficientShortComplex a n).Exact := by
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  intro x hx
  change Ideal.Quotient.mk (Ideal.span {a ^ n}) x = 0 at hx
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp ((Ideal.Quotient.eq_zero_iff_mem).mp hx)
  exact ⟨r, hr.symm⟩

variable (K : CochainComplex (ModuleCat.{u} R) ℤ)

/-- The standard quotient-coefficient map on the original complex. -/
def powerQuotientTensorMap (n : ℕ) :
    K ⟶ (moduleTensorCochainFunctor K).obj (ModuleCat.of R (R ⧸ Ideal.span {a ^ n})) :=
  (moduleTensorCochainUnitIso K).inv ≫
    (moduleTensorCochainFunctor K).map (powerQuotientCoefficientMap a n)

lemma powerQuotientTensorMap_zero (n : ℕ) :
    smulId (a ^ n) K ≫ powerQuotientTensorMap a K n = 0 := by
  let F := moduleTensorCochainFunctor K
  let e := moduleTensorCochainUnitIso K
  calc
    smulId (a ^ n) K ≫ powerQuotientTensorMap a K n =
        e.inv ≫ (F.map (a ^ n • 𝟙 (ModuleCat.of R R)) ≫
          F.map (powerQuotientCoefficientMap a n)) := by
      simp [powerQuotientTensorMap, F, e, smulId, Linear.smul_comp, Linear.comp_smul]
    _ = 0 := by
      rw [← F.map_comp, (powerQuotientCoefficientShortComplex a n).zero, F.map_zero, comp_zero]

abbrev powerQuotientTensorShortComplex (n : ℕ) :
    ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ) :=
  ShortComplex.mk (smulId (a ^ n) K) (powerQuotientTensorMap a K n)
    (powerQuotientTensorMap_zero a K n)

lemma powerQuotientTensorShortComplex_exact (hK : ∀ i, Module.Flat R (K.X i)) (n : ℕ) :
    (powerQuotientTensorShortComplex a K n).Exact := by
  let F := moduleTensorCochainFunctor K
  let e := moduleTensorCochainUnitIso K
  let hS := moduleTensorCochain_exact K hK (powerQuotientCoefficientShortComplex a n)
    (powerQuotientCoefficientShortComplex_exact a n)
  let ei : (powerQuotientCoefficientShortComplex a n).map F ≅
      powerQuotientTensorShortComplex a K n :=
    ShortComplex.isoMk e e (Iso.refl _)
      (by simp [smulId, F, Linear.comp_smul, Linear.smul_comp])
      (by simp [powerQuotientTensorMap, e, F])
  exact ShortComplex.exact_of_iso ei hS

instance powerQuotientTensorMap_epi (n : ℕ) : Epi (powerQuotientTensorMap a K n) := by
  have := moduleTensorCochain_map_epi K (powerQuotientCoefficientMap a n)
  dsimp only [powerQuotientTensorMap]
  infer_instance

/-- In a flat model, the actual categorical cokernel equals tensoring the
original model with the ordinary quotient module. -/
def powerCokernelTensorModelIso (hK : ∀ i, Module.Flat R (K.X i)) (n : ℕ) :
    powerCokernelComplex a K n ≅
      (moduleTensorCochainFunctor K).obj (ModuleCat.of R (R ⧸ Ideal.span {a ^ n})) :=
  (cokernelIsCokernel (smulId (a ^ n) K)).coconePointUniqueUpToIso
    (powerQuotientTensorShortComplex_exact a K hK n).gIsCokernel

@[reassoc] lemma powerCokernelTensorModelIso_π (hK : ∀ i, Module.Flat R (K.X i)) (n : ℕ) :
    cokernel.π (smulId (a ^ n) K) ≫ (powerCokernelTensorModelIso a K hK n).hom =
      powerQuotientTensorMap a K n :=
  IsColimit.comp_coconePointUniqueUpToIso_hom
    (cokernelIsCokernel (smulId (a ^ n) K))
    (powerQuotientTensorShortComplex_exact a K hK n).gIsCokernel WalkingParallelPair.one

end SerrePositivity.DerivedCompletion
