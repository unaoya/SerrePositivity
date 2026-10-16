module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModulePowerTorAlgebraMilnor
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PowerCokernelNaturality
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.MilnorNaturality

/-! # Coefficient actions on both original Milnor endpoints -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory MonoidalCategory
variable {R : Type u} [CommRing R] (a : R)
  (C : Type u) [CommRing C] [Algebra R C] (M : ModuleCat.{u} R)
local notation "K₀" => CategoryTheory.Functor.obj (moduleTensorCochainFunctor
  (extRes (projectiveResolution (ModuleCat.of R C)))) M

/-- The original lift of coefficient multiplication in the unresolved-test tensor model. -/
abbrev modulePowerCoefficientLift (c : C) : K₀ ⟶ K₀ :=
  ((tensorLeft M).mapHomologicalComplex (.up ℤ)).map
    (extLift (projectiveResolution (ModuleCat.of R C)) (ModuleCat.ofHom (LinearMap.mulLeft R c))
      (projectiveResolution (ModuleCat.of R C)))

/-- The original induced endomorphism of the original Milnor short complex. -/
def modulePowerCokernelMilnorScalarMap (c : C) (j : ℤ) :
    complexTowerMilnorSequence R (powerCokernelComplex a K₀)
      (powerCokernelComplexTransition a K₀) j ⟶
    complexTowerMilnorSequence R (powerCokernelComplex a K₀)
      (powerCokernelComplexTransition a K₀) j :=
  complexTowerMilnorSequenceMap R _ _
    (powerCokernelMap a (modulePowerCoefficientLift C M c))
    (powerCokernelMap_transition a (modulePowerCoefficientLift C M c)) j

lemma modulePowerCokernelTorAlgebraLimitComparison_scalar (i : ℕ) (c : C)
    (x : moduleTowerLimit R (fun n => (powerCokernelComplex a K₀ n).homology (-(i : ℤ)))
      (fun n => (HomologicalComplex.homologyMap
        (powerCokernelComplexTransition a K₀ n) (-(i : ℤ))).hom)) :
    modulePowerCokernelTorAlgebraLimitComparison a C M i
      (complexTowerHomologyLimitMap R _ _
        (powerCokernelMap a (modulePowerCoefficientLift C M c))
        (powerCokernelMap_transition a (modulePowerCoefficientLift C M c)) (-(i : ℤ)) x) =
      (ModuleCat.restrictScalars (algebraMap R C)).map
        (c • 𝟙 (modulePowerTorAlgebraLimit a C M i))
        (modulePowerCokernelTorAlgebraLimitComparison a C M i x) := by
  apply Subtype.ext
  funext n
  rw [modulePowerCokernelTorAlgebraLimitComparison_apply]
  change (modulePowerCokernelTorAlgebraIso a C M n i).hom
      (HomologicalComplex.homologyMap (modulePowerTensorCokernelMap a M
        (extLift (projectiveResolution (ModuleCat.of R C))
          (ModuleCat.ofHom (LinearMap.mulLeft R c)) (projectiveResolution (ModuleCat.of R C))) n)
        (-(i : ℤ)) (x.val n)) = _
  exact congrArg (fun f => f.hom (x.val n)) (modulePowerCokernelTorAlgebraIso_scalar a C M n i c)

lemma modulePowerCokernelTorAlgebraLimOneComparison_scalar (i : ℕ) (c : C)
    (x : complexTowerHomologyLimOne R (powerCokernelComplex a K₀)
      (powerCokernelComplexTransition a K₀) (-(i : ℤ))) :
    modulePowerCokernelTorAlgebraLimOneComparison a C M i
      (complexTowerHomologyLimOneMap R _ _
        (powerCokernelMap a (modulePowerCoefficientLift C M c))
        (powerCokernelMap_transition a (modulePowerCoefficientLift C M c)) (-(i : ℤ)) x) =
      (ModuleCat.restrictScalars (algebraMap R C)).map
        (c • 𝟙 (modulePowerTorAlgebraLimOne a C M i))
        (modulePowerCokernelTorAlgebraLimOneComparison a C M i x) := by
  induction x using Submodule.Quotient.induction_on with
  | _ y =>
    change modulePowerCokernelTorAlgebraLimOneComparison a C M i
      (Submodule.Quotient.mk (fun n => HomologicalComplex.homologyMap
        (powerCokernelMap a (modulePowerCoefficientLift C M c) n) (-(i : ℤ)) (y n))) = _
    rw [modulePowerCokernelTorAlgebraLimOneComparison_mk,
      modulePowerCokernelTorAlgebraLimOneComparison_mk]
    change Submodule.Quotient.mk _ = Submodule.Quotient.mk
      (c • (fun n => (modulePowerCokernelTorAlgebraIso a C M n i).hom (y n)))
    congr 1
    funext n
    exact congrArg (fun f => f.hom (y n)) (modulePowerCokernelTorAlgebraIso_scalar a C M n i c)

/-- Reindex the original lim¹ endpoint by an explicit cochain/Tor degree equality. -/
def modulePowerCokernelTorAlgebraLimOneIsoAt (j : ℤ) (i : ℕ) (hj : j = -(i : ℤ)) :
    ModuleCat.of R (complexTowerHomologyLimOne R (powerCokernelComplex a K₀)
      (powerCokernelComplexTransition a K₀) j) ≅
      (ModuleCat.restrictScalars (algebraMap R C)).obj (modulePowerTorAlgebraLimOne a C M i) := by
  subst j
  exact (modulePowerCokernelTorAlgebraLimOneComparison a C M i).toModuleIso

@[reassoc] lemma modulePowerCokernelTorAlgebraLimOneIsoAt_scalar
    (j : ℤ) (i : ℕ) (hj : j = -(i : ℤ)) (c : C) :
    ModuleCat.ofHom (complexTowerHomologyLimOneMap R _ _
      (powerCokernelMap a (modulePowerCoefficientLift C M c))
      (powerCokernelMap_transition a (modulePowerCoefficientLift C M c)) j) ≫
        (modulePowerCokernelTorAlgebraLimOneIsoAt a C M j i hj).hom =
      (modulePowerCokernelTorAlgebraLimOneIsoAt a C M j i hj).hom ≫
        (ModuleCat.restrictScalars (algebraMap R C)).map
          (c • 𝟙 (modulePowerTorAlgebraLimOne a C M i)) := by
  subst j
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact modulePowerCokernelTorAlgebraLimOneComparison_scalar a C M i c x

end SerrePositivity.DerivedCompletion
