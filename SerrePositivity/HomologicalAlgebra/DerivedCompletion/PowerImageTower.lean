module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PowerTorsionComplex
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.TowerExact
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.LocalizationTowerComparison

/-! # Image and ordinary cokernel towers for multiplication by powers -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {R : Type u} [CommRing R] (a : R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ)

/-- The ordinary cokernel complex; no regularity hypothesis is imposed. -/
abbrev powerCokernelComplex (n : ℕ) := cokernel (smulId (a ^ n) K)

/-- The image complex, keeping the actual differential and categorical image. -/
abbrev powerImageComplex (n : ℕ) := Abelian.image (smulId (a ^ n) K)

/-- Standard transition square: a on the source and identity on the target. -/
lemma powerScalar_square (n : ℕ) :
    smulId a K ≫ smulId (a ^ n) K = smulId (a ^ (n + 1)) K ≫ 𝟙 K := by
  simp [smulId, Linear.comp_smul, smul_smul, pow_succ, mul_comm]

def powerCokernelComplexTransition (n : ℕ) :
    powerCokernelComplex a K (n + 1) ⟶ powerCokernelComplex a K n :=
  cokernel.map _ _ (smulId a K) (𝟙 K) (powerScalar_square a K n).symm

def powerImageComplexTransition (n : ℕ) :
    powerImageComplex a K (n + 1) ⟶ powerImageComplex a K n :=
  kernel.map _ _ (𝟙 K) (powerCokernelComplexTransition a K n) (by
    simp [powerCokernelComplexTransition])

@[reassoc] lemma powerImageComplexTransition_ι (n : ℕ) :
    powerImageComplexTransition a K n ≫ Abelian.image.ι (smulId (a ^ n) K) =
      Abelian.image.ι (smulId (a ^ (n + 1)) K) := by
  simp [powerImageComplexTransition]

@[reassoc] lemma powerImageComplexTransition_factor (n : ℕ) :
    smulId a K ≫ Abelian.factorThruImage (smulId (a ^ n) K) =
      Abelian.factorThruImage (smulId (a ^ (n + 1)) K) ≫ powerImageComplexTransition a K n := by
  apply (cancel_mono (Abelian.image.ι (smulId (a ^ n) K))).mp
  simp only [Category.assoc, powerImageComplexTransition_ι, Abelian.image.fac]
  simpa using powerScalar_square a K n

/-- The original inclusion of termwise torsion into the original complex. -/
def powerTorsionComplexInclusion (n : ℕ) : powerTorsionComplex a K n ⟶ K where
  f i := ModuleCat.ofHom (powerTorsionModule a (K.X i) n).subtype
  comm' _ _ _ := rfl

@[reassoc] lemma powerTorsionComplexInclusion_transition (n : ℕ) :
    powerTorsionComplexTransition a K n ≫ powerTorsionComplexInclusion a K n =
      powerTorsionComplexInclusion a K (n + 1) ≫ smulId a K := rfl

lemma powerTorsionComplexInclusion_factor_zero (n : ℕ) :
    powerTorsionComplexInclusion a K n ≫ Abelian.factorThruImage (smulId (a ^ n) K) = 0 := by
  apply (cancel_mono (Abelian.image.ι (smulId (a ^ n) K))).mp
  rw [Category.assoc, Abelian.image.fac, zero_comp]
  apply HomologicalComplex.hom_ext
  intro i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact x.property

/-- Torsion → original complex → image is a genuine short complex. -/
abbrev powerTorsionImageShortComplex (n : ℕ) : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ) :=
  ShortComplex.mk (powerTorsionComplexInclusion a K n)
    (Abelian.factorThruImage (smulId (a ^ n) K)) (powerTorsionComplexInclusion_factor_zero a K n)

lemma powerTorsionImageShortComplex_shortExact (n : ℕ) :
    (powerTorsionImageShortComplex a K n).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · apply (ShortComplex.moduleCat_exact_iff _).mpr
    intro x hx
    change (Abelian.factorThruImage (smulId (a ^ n) K)).f i x = 0 at hx
    have hfac := congrArg (fun f ↦ (f.f i).hom x) (Abelian.image.fac (smulId (a ^ n) K))
    have hscalar : a ^ n • x = 0 := by
      change ((Abelian.image.ι (smulId (a ^ n) K)).f i)
        ((Abelian.factorThruImage (smulId (a ^ n) K)).f i x) = a ^ n • x at hfac
      rw [hx, map_zero] at hfac
      exact hfac.symm
    exact ⟨⟨x, hscalar⟩, rfl⟩
  · exact (ModuleCat.mono_iff_injective _).mpr Subtype.val_injective
  · change Epi ((Abelian.factorThruImage (smulId (a ^ n) K)).f i)
    infer_instance

/-- Image → original complex → ordinary cokernel is short exact. -/
abbrev powerImageCokernelShortComplex (n : ℕ) :
    ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ) :=
  ShortComplex.mk (Abelian.image.ι (smulId (a ^ n) K)) (cokernel.π (smulId (a ^ n) K))
    (kernel.condition _)

lemma powerImageCokernelShortComplex_shortExact (n : ℕ) :
    (powerImageCokernelShortComplex a K n).ShortExact :=
  { exact := ShortComplex.exact_kernel _, mono_f := inferInstance, epi_g := inferInstance }

end SerrePositivity.DerivedCompletion
