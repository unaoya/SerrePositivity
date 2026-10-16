module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.TowerHomologyNaturality

/-! # The actual Milnor short exact sequence under arbitrary tower maps -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits
variable (R : Type u) [CommRing R]
    {K L : ℕ → CochainComplex (ModuleCat.{u} R) ℤ}
    (t : ∀ n, K (n + 1) ⟶ K n) (s : ∀ n, L (n + 1) ⟶ L n)
    (g : ∀ n, K n ⟶ L n) (hg : ∀ n, t n ≫ g n = g (n + 1) ≫ s n)

/-- The componentwise map on the original homology products. -/
def complexTowerHomologyProductMap (i : ℤ) :
    (∀ n, (K n).homology i) →ₗ[R] ∀ n, (L n).homology i :=
  LinearMap.pi (fun n => (HomologicalComplex.homologyMap (g n) i).hom.comp (LinearMap.proj n))

@[simp] lemma complexTowerHomologyProductMap_apply (i : ℤ)
    (y : ∀ n, (K n).homology i) (n : ℕ) :
    complexTowerHomologyProductMap R g i y n = HomologicalComplex.homologyMap (g n) i (y n) := rfl

include hg in
lemma complexTowerHomologyDifference_naturality (i : ℤ) (y : ∀ n, (K n).homology i) :
    complexTowerHomologyProductMap R g i (complexTowerHomologyDifference R K t i y) =
      complexTowerHomologyDifference R L s i (complexTowerHomologyProductMap R g i y) := by
  ext n
  have h := congrArg (fun f => HomologicalComplex.homologyMap f i) (hg n)
  simp only [HomologicalComplex.homologyMap_comp] at h
  have hx := congrArg (fun f => f.hom (y (n + 1))) h
  simpa only [complexTowerHomologyProductMap_apply, complexTowerHomologyDifference,
    moduleTowerDifference_apply, map_sub, ModuleCat.comp_apply] using congrArg (fun z =>
      HomologicalComplex.homologyMap (g n) i (y n) - z) hx

/-- The original difference cokernels, with the induced map rather than a new lim¹. -/
def complexTowerHomologyLimOneMap (i : ℤ) :
    complexTowerHomologyLimOne R K t i →ₗ[R] complexTowerHomologyLimOne R L s i :=
  (complexTowerHomologyDifference R K t i).range.mapQ
    (complexTowerHomologyDifference R L s i).range (complexTowerHomologyProductMap R g i)
    (by
      rintro y ⟨z, rfl⟩
      exact ⟨complexTowerHomologyProductMap R g i z,
        (complexTowerHomologyDifference_naturality R t s g hg i z).symm⟩)

/-- The induced map on the original compatible homology sequences. -/
def complexTowerHomologyLimitMap (i : ℤ) :
    moduleTowerLimit R (fun n => (K n).homology i)
      (fun n => (HomologicalComplex.homologyMap (t n) i).hom) →ₗ[R]
    moduleTowerLimit R (fun n => (L n).homology i)
      (fun n => (HomologicalComplex.homologyMap (s n) i).hom) :=
  ((complexTowerHomologyProductMap R g i).comp
    (moduleTowerLimit R (fun n => (K n).homology i)
      (fun n => (HomologicalComplex.homologyMap (t n) i).hom)).subtype).codRestrict _ (by
        intro x
        change complexTowerHomologyDifference R L s i
          (complexTowerHomologyProductMap R g i x.val) = 0
        rw [← complexTowerHomologyDifference_naturality R t s g hg]
        have hx : complexTowerHomologyDifference R K t i x.val = 0 := x.property
        rw [hx, map_zero])

lemma complexTowerMilnorInclusion_naturality (i : ℤ)
    (y : complexTowerHomologyLimOne R K t (i - 1)) :
    HomologicalComplex.homologyMap (complexTowerHomotopyLimitMap R t s g hg) i
      (complexTowerMilnorInclusion R K t i y) =
        complexTowerMilnorInclusion R L s i (complexTowerHomologyLimOneMap R t s g hg (i - 1) y) := by
  induction y using Submodule.Quotient.induction_on with
  | _ y => exact complexTowerHomologyIncoming_naturality R t s g hg i y

lemma complexTowerMilnorProjection_naturality (i : ℤ)
    (x : (complexTowerHomotopyLimit R K t).homology i) :
    complexTowerMilnorProjection R L s i
      (HomologicalComplex.homologyMap (complexTowerHomotopyLimitMap R t s g hg) i x) =
        complexTowerHomologyLimitMap R t s g hg i (complexTowerMilnorProjection R K t i x) := by
  apply Subtype.ext
  exact complexTowerHomologyBoundary_naturality R t s g hg i x

/-- A genuine morphism of the existing Milnor short complexes. -/
def complexTowerMilnorSequenceMap (i : ℤ) :
    complexTowerMilnorSequence R K t i ⟶ complexTowerMilnorSequence R L s i :=
  { τ₁ := ModuleCat.ofHom (complexTowerHomologyLimOneMap R t s g hg (i - 1))
    τ₂ := HomologicalComplex.homologyMap (complexTowerHomotopyLimitMap R t s g hg) i
    τ₃ := ModuleCat.ofHom (complexTowerHomologyLimitMap R t s g hg i)
    comm₁₂ := by ext y; exact (complexTowerMilnorInclusion_naturality R t s g hg i y).symm
    comm₂₃ := by ext x; exact complexTowerMilnorProjection_naturality R t s g hg i x }

end SerrePositivity.DerivedCompletion
