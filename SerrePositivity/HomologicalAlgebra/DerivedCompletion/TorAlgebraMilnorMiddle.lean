module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.FiniteCoefficientCokernelHolim
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModulePowerTorAlgebraMilnor

/-! # The original Milnor middle and the actual coefficient-algebra Tor module -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory MonoidalCategory
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R] [IsRegularLocalRing R] (a : R)
  (C : Type u) [CommRing C] [Algebra R C] (M : ModuleCat.{u} R) [Module.Finite R M]
local notation "C₀" => ModuleCat.of R C
local notation "K₀" => finiteCoefficientTensorModel R C₀ M
local notation "L₀" => complexTowerHomotopyLimit R (powerCokernelComplex a K₀)
  (powerCokernelComplexTransition a K₀)

/-- The actual middle cohomology of the original Milnor sequence, compared to
algebra-valued Tor through the original reconstruction. -/
def torAlgebraMilnorMiddleIso (hC : IsModuleComplete R a C₀) (i : ℕ) :
    (L₀).homology (-(i : ℤ)) ≅ (ModuleCat.restrictScalars (algebraMap R C)).obj
      (((ModuleCat.extendScalars (algebraMap R C)).leftDerived i).obj M) :=
  (DerivedCategory.homologyFunctorFactors (ModuleCat R) (-(i : ℤ))).symm.app L₀ ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat R) (-(i : ℤ))).mapIso
      (finiteCoefficientPowerCokernelHolimIso a C₀ M hC).symm ≪≫
        (boundedAboveDerivedTensorModuleTorNatIso C₀ i).app M ≪≫ torAlgebraComparison M i

/-- The original lifted coefficient multiplication on holim becomes exactly the
scalar action on the actual C-module Tor. -/
@[reassoc] lemma torAlgebraMilnorMiddleIso_scalar
    (hC : IsModuleComplete R a C₀) (i : ℕ) (c : C) :
    HomologicalComplex.homologyMap (powerCokernelHolimMap a
      (((tensorLeft M).mapHomologicalComplex (.up ℤ)).map
        (extLift (projectiveResolution C₀) (ModuleCat.ofHom (LinearMap.mulLeft R c))
          (projectiveResolution C₀)))) (-(i : ℤ)) ≫
        (torAlgebraMilnorMiddleIso a C M hC i).hom =
      (torAlgebraMilnorMiddleIso a C M hC i).hom ≫
        (ModuleCat.restrictScalars (algebraMap R C)).map
          (c • 𝟙 (((ModuleCat.extendScalars (algebraMap R C)).leftDerived i).obj M)) := by
  let H := DerivedCategory.homologyFunctor (ModuleCat R) (-(i : ℤ))
  let f : C₀ ⟶ C₀ := ModuleCat.ofHom (LinearMap.mulLeft R c)
  let k := powerCokernelHolimMap a (((tensorLeft M).mapHomologicalComplex (.up ℤ)).map
    (extLift (projectiveResolution C₀) f (projectiveResolution C₀)))
  let d := (boundedAboveDerivedTensor.map (CategoryTheory.Prod.mkHom
    (boundedAboveDerivedSingleFunctor.map f) (𝟙 (boundedAboveDerivedSingleFunctor.obj M)))).hom
  let e := finiteCoefficientPowerCokernelHolimIso a C₀ M hC
  let q := (DerivedCategory.homologyFunctorFactors (ModuleCat R) (-(i : ℤ))).symm.app L₀
  let t := (boundedAboveDerivedTensorModuleTorNatIso C₀ i).app M
  let b := torAlgebraComparison (C := C) M i
  have hn : d ≫ e.hom = e.hom ≫ DerivedCategory.Q.map k :=
    finiteCoefficientPowerCokernelHolimIso_naturality_left a C₀ M f hC hC
  have hni : DerivedCategory.Q.map k ≫ e.inv = e.inv ≫ d := by
    apply (cancel_epi e.hom).mp
    rw [← Category.assoc, ← hn, Category.assoc, Iso.hom_inv_id, Category.comp_id,
      Iso.hom_inv_id_assoc]
  have h₂ := congrArg H.map hni
  simp only [Functor.map_comp] at h₂
  have h₁ := (DerivedCategory.homologyFunctorFactors (ModuleCat R) (-(i : ℤ))).inv.naturality k
  change HomologicalComplex.homologyMap k (-(i : ℤ)) ≫ q.hom =
    q.hom ≫ H.map (DerivedCategory.Q.map k) at h₁
  have h₃ := boundedAboveDerivedTensorModuleTorIso_naturality_left f M i
  change H.map d ≫ t.hom = t.hom ≫ torCoefficientScalarEndomorphism C M i c at h₃
  have h₄ := torAlgebraComparison_coefficient_scalar M i c
  change HomologicalComplex.homologyMap k (-(i : ℤ)) ≫
    (q.hom ≫ H.map e.inv ≫ t.hom ≫ b.hom) =
      (q.hom ≫ H.map e.inv ≫ t.hom ≫ b.hom) ≫ _
  rw [reassoc_of% h₁, reassoc_of% h₂, reassoc_of% h₃, h₄]
  simp only [Category.assoc]
  rfl

end SerrePositivity.DerivedCompletion
