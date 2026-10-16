module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModulePowerReduction
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PowerCokernelTransitions

/-! # Ordinary module power quotients in a fixed flat tensor model

The test module is unresolved and may have torsion. All maps are induced by
the original quotient maps, and the comparison retains their transitions.
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex
variable {R : Type u} [CommRing R] (a : R) (M : ModuleCat.{u} R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ)

/-- Tensor the original map M → M/aⁿM with the same complex K. -/
def modulePowerTensorReductionMap (n : ℕ) :
    (moduleTensorCochainFunctor K).obj M ⟶
      (moduleTensorCochainFunctor K).obj (modulePowerReduction a M n) :=
  (moduleTensorCochainFunctor K).map (modulePowerReductionMap a M n)

lemma modulePowerTensorReductionMap_zero (n : ℕ) :
    smulId (a ^ n) ((moduleTensorCochainFunctor K).obj M) ≫
      modulePowerTensorReductionMap a M K n = 0 := by
  let F := moduleTensorCochainFunctor K
  have he : smulId (a ^ n) (F.obj M) = F.map (a ^ n • 𝟙 M) := by
    simp [smulId]
  rw [he]
  change F.map (a ^ n • 𝟙 M) ≫ F.map (modulePowerReductionMap a M n) = 0
  rw [← F.map_comp, modulePowerReductionMap_zero, F.map_zero]

abbrev modulePowerTensorReductionShortComplex (n : ℕ) :
    ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ) :=
  ShortComplex.mk (smulId (a ^ n) ((moduleTensorCochainFunctor K).obj M))
    (modulePowerTensorReductionMap a M K n) (modulePowerTensorReductionMap_zero a M K n)

lemma modulePowerTensorReductionShortComplex_exact
    (hK : ∀ i, Module.Flat R (K.X i)) (n : ℕ) :
    (modulePowerTensorReductionShortComplex a M K n).Exact := by
  let F := moduleTensorCochainFunctor K
  let e : (modulePowerReductionShortComplex a M n).map F ≅
      modulePowerTensorReductionShortComplex a M K n :=
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp [smulId, F]) (by simp [modulePowerTensorReductionMap, F])
  exact ShortComplex.exact_of_iso e
    (moduleTensorCochain_exact K hK _ (modulePowerReductionShortComplex_exact a M n))

instance modulePowerTensorReductionMap_epi (n : ℕ) :
    Epi (modulePowerTensorReductionMap a M K n) :=
  moduleTensorCochain_map_epi K (modulePowerReductionMap a M n)

/-- Each ordinary power cokernel in M ⊗ K is the actual tensor of M/aⁿM with K. -/
def modulePowerTensorModelIso (hK : ∀ i, Module.Flat R (K.X i)) (n : ℕ) :
    powerCokernelComplex a ((moduleTensorCochainFunctor K).obj M) n ≅
      (moduleTensorCochainFunctor K).obj (modulePowerReduction a M n) :=
  (cokernelIsCokernel _).coconePointUniqueUpToIso
    (modulePowerTensorReductionShortComplex_exact a M K hK n).gIsCokernel

@[reassoc] lemma modulePowerTensorModelIso_π
    (hK : ∀ i, Module.Flat R (K.X i)) (n : ℕ) :
    cokernel.π (smulId (a ^ n) ((moduleTensorCochainFunctor K).obj M)) ≫
      (modulePowerTensorModelIso a M K hK n).hom =
        modulePowerTensorReductionMap a M K n :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (cokernelIsCokernel _)
    (modulePowerTensorReductionShortComplex_exact a M K hK n).gIsCokernel
    WalkingParallelPair.one

/-- The comparison identifies the original tower transition with the ordinary
reduction transition induced by the identity of M. -/
@[reassoc] lemma modulePowerTensorModelIso_transition
    (hK : ∀ i, Module.Flat R (K.X i)) (n : ℕ) :
    powerCokernelComplexTransition a ((moduleTensorCochainFunctor K).obj M) n ≫
        (modulePowerTensorModelIso a M K hK n).hom =
      (modulePowerTensorModelIso a M K hK (n + 1)).hom ≫
        (moduleTensorCochainFunctor K).map (modulePowerReductionTransition a M n) := by
  apply (cancel_epi (cokernel.π
    (smulId (a ^ (n + 1)) ((moduleTensorCochainFunctor K).obj M)))).mp
  rw [← Category.assoc, powerCokernelComplexTransition_π, modulePowerTensorModelIso_π]
  rw [← Category.assoc, modulePowerTensorModelIso_π]
  simp only [modulePowerTensorReductionMap, ← Functor.map_comp,
    modulePowerReductionTransition_π]

variable {K} {L : CochainComplex (ModuleCat.{u} R) ℤ}

/-- Changing the fixed complex induces the original cokernel map at each stage. -/
def modulePowerTensorCokernelMap (f : K ⟶ L) (n : ℕ) :
    powerCokernelComplex a ((moduleTensorCochainFunctor K).obj M) n ⟶
      powerCokernelComplex a ((moduleTensorCochainFunctor L).obj M) n :=
  cokernel.map _ _
    (((tensorLeft M).mapHomologicalComplex (.up ℤ)).map f)
    (((tensorLeft M).mapHomologicalComplex (.up ℤ)).map f)
    (by simp [smulId, Linear.smul_comp, Linear.comp_smul])

/-- Naturality includes arbitrary coefficient-resolution maps, hence in
particular the original lifts of multiplication by coefficient scalars. -/
@[reassoc] lemma modulePowerTensorModelIso_naturality
    (f : K ⟶ L) (hK : ∀ i, Module.Flat R (K.X i))
    (hL : ∀ i, Module.Flat R (L.X i)) (n : ℕ) :
    modulePowerTensorCokernelMap a M f n ≫ (modulePowerTensorModelIso a M L hL n).hom =
      (modulePowerTensorModelIso a M K hK n).hom ≫
        (((tensorLeft (modulePowerReduction a M n)).mapHomologicalComplex (.up ℤ)).map f) := by
  apply (cancel_epi (cokernel.π
    (smulId (a ^ n) ((moduleTensorCochainFunctor K).obj M)))).mp
  rw [← Category.assoc]
  simp only [modulePowerTensorCokernelMap, cokernel.map, cokernel.π_desc,
    Category.assoc, modulePowerTensorModelIso_π]
  rw [modulePowerTensorModelIso_π_assoc]
  change (((tensorLeft M).mapHomologicalComplex (.up ℤ)).map f) ≫
      modulePowerTensorReductionMap a M L n =
    modulePowerTensorReductionMap a M K n ≫ _
  exact (NatTrans.mapHomologicalComplex
    ((tensoringLeft (ModuleCat R)).map (modulePowerReductionMap a M n)) (.up ℤ)).naturality f

end SerrePositivity.DerivedCompletion
