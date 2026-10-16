module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.FiniteCoefficientPowerHolim
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.TowerLiftNaturality

/-! # Coefficient morphisms act on the original ordinary-quotient holim

The coefficient morphism may in particular be multiplication by an element of
an R-algebra; it is not restricted to a scalar in the base ring R.
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits MonoidalCategory
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R] (a : R) (M : ModuleCat.{u} R)
    {K L : CochainComplex (ModuleCat.{u} R) ℤ}

/-- Original quotient transitions commute with every coefficient-complex map. -/
lemma modulePowerTensorTransition_naturality (f : K ⟶ L) (n : ℕ) :
    modulePowerTensorTransition a M K n ≫
        (((tensorLeft (modulePowerReduction a M n)).mapHomologicalComplex (.up ℤ)).map f) =
      (((tensorLeft (modulePowerReduction a M (n + 1))).mapHomologicalComplex (.up ℤ)).map f) ≫
        modulePowerTensorTransition a M L n :=
  (NatTrans.mapHomologicalComplex
    ((tensoringLeft (ModuleCat R)).map (modulePowerReductionTransition a M n)) (.up ℤ)).naturality f |>.symm

/-- The coefficient-complex map induces a map of the same ordinary-quotient holims. -/
def modulePowerTensorHolimMap (f : K ⟶ L) :
    complexTowerHomotopyLimit R (modulePowerTensorTower a M K) (modulePowerTensorTransition a M K) ⟶
      complexTowerHomotopyLimit R (modulePowerTensorTower a M L) (modulePowerTensorTransition a M L) :=
  complexTowerHomotopyLimitMap R (modulePowerTensorTransition a M K)
    (modulePowerTensorTransition a M L)
    (fun n => ((tensorLeft (modulePowerReduction a M n)).mapHomologicalComplex (.up ℤ)).map f)
    (modulePowerTensorTransition_naturality a M f)

/-- Reconstruction intertwines the original coefficient action and its tower action. -/
@[reassoc] lemma modulePowerTensorReconstruction_naturality (f : K ⟶ L) :
    modulePowerTensorReconstruction a M K ≫ modulePowerTensorHolimMap a M f =
      (((tensorLeft M).mapHomologicalComplex (.up ℤ)).map f) ≫
        modulePowerTensorReconstruction a M L := by
  apply complexTowerCompatibleLift_naturality
  intro n
  exact ((NatTrans.mapHomologicalComplex
    ((tensoringLeft (ModuleCat R)).map (modulePowerReductionMap a M n)) (.up ℤ)).naturality f).symm

/-- The actual coefficient morphism, lifted to the original fixed resolutions. -/
def modulePowerDerivedTensorHolimMap {C D : ModuleCat.{u} R} (f : C ⟶ D) :
    DerivedCategory.Q.obj (modulePowerDerivedTensorHolimComplex R a C M) ⟶
      DerivedCategory.Q.obj (modulePowerDerivedTensorHolimComplex R a D M) :=
  DerivedCategory.Q.map (modulePowerTensorHolimMap a M
    (extLift (projectiveResolution C) f (projectiveResolution D)))

/-- The actual derived reconstruction preserves arbitrary coefficient morphisms. -/
@[reassoc] lemma finiteCoefficientPowerHolimIso_naturality_left
    [IsRegularLocalRing R] [Module.Finite R M]
    {C D : ModuleCat.{u} R} (f : C ⟶ D)
    (hC : IsModuleComplete R a C) (hD : IsModuleComplete R a D) :
    (boundedAboveDerivedTensor.map (CategoryTheory.Prod.mkHom
      (boundedAboveDerivedSingleFunctor.map f)
      (𝟙 (boundedAboveDerivedSingleFunctor.obj M)))).hom ≫
        (finiteCoefficientPowerHolimIso R a D M hD).hom =
      (finiteCoefficientPowerHolimIso R a C M hC).hom ≫
        modulePowerDerivedTensorHolimMap a M f := by
  have hn := derivedTensorCoefficientModelIso_naturality_left M f
  have hr := modulePowerTensorReconstruction_naturality a M
    (extLift (projectiveResolution C) f (projectiveResolution D))
  simp only [finiteCoefficientPowerHolimIso, Iso.trans_hom, asIso_hom,
    modulePowerDerivedTensorHolimMap]
  rw [← Category.assoc, hn, Category.assoc, ← Functor.map_comp,
    ← hr, Functor.map_comp, ← Category.assoc]

end SerrePositivity.DerivedCompletion
