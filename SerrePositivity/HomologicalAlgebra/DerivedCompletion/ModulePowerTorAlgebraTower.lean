module

public import SerrePositivity.HomologicalAlgebra.TorAlgebraNaturality
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModulePowerReduction
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleTowerEquiv
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleClosure

/-! # The ordinary-quotient Tor tower as actual coefficient-algebra modules

Stages and transitions use the existing algebra-valued left derived functor.
Their actual limit and lim¹ are complete without assuming that lim¹ vanishes.
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
variable {R : Type u} [CommRing R] (a : R)
    (C : Type u) [CommRing C] [Algebra R C] (M : ModuleCat.{u} R) (i : ℕ)

abbrev modulePowerTorAlgebraTower (n : ℕ) : ModuleCat.{u} C :=
  ((ModuleCat.extendScalars (algebraMap R C)).leftDerived i).obj (modulePowerReduction a M n)

def modulePowerTorAlgebraTransition (n : ℕ) :
    modulePowerTorAlgebraTower a C M i (n + 1) ⟶ modulePowerTorAlgebraTower a C M i n :=
  ((ModuleCat.extendScalars (algebraMap R C)).leftDerived i).map (modulePowerReductionTransition a M n)

lemma modulePowerTorAlgebra_pow_smul_zero (n : ℕ) (x : modulePowerTorAlgebraTower a C M i n) :
    (algebraMap R C a) ^ n • x = 0 := by
  simpa only [map_pow] using torAlg_smul_eq_zero (algebraMap R C) i
    (modulePowerReduction a M n) (a ^ n) (modulePowerReduction_pow_smul_zero a M n) x

lemma modulePowerTorAlgebra_isModuleComplete (n : ℕ) :
    IsModuleComplete C (algebraMap R C a) (modulePowerTorAlgebraTower a C M i n) :=
  isModuleComplete_of_pow_smul_zero C (algebraMap R C a) _ n
    (modulePowerTorAlgebra_pow_smul_zero a C M i n)

abbrev modulePowerTorAlgebraLimit : ModuleCat.{u} C :=
  ModuleCat.of C (moduleTowerLimit C (fun n => modulePowerTorAlgebraTower a C M i n)
    (fun n => (modulePowerTorAlgebraTransition a C M i n).hom))

abbrev modulePowerTorAlgebraLimOne : ModuleCat.{u} C :=
  ModuleCat.of C ((∀ n, modulePowerTorAlgebraTower a C M i n) ⧸
    (moduleTowerDifference C (fun n => modulePowerTorAlgebraTower a C M i n)
      (fun n => (modulePowerTorAlgebraTransition a C M i n).hom)).range)

lemma modulePowerTorAlgebraLimit_isModuleComplete :
    IsModuleComplete C (algebraMap R C a) (modulePowerTorAlgebraLimit a C M i) := by
  have hp := isModuleComplete_pi C (algebraMap R C a)
    (modulePowerTorAlgebraTower a C M i) (modulePowerTorAlgebra_isModuleComplete a C M i)
  exact isModuleComplete_ker C (algebraMap R C a)
    (M := ModuleCat.of C (∀ n, modulePowerTorAlgebraTower a C M i n))
    (N := ModuleCat.of C (∀ n, modulePowerTorAlgebraTower a C M i n)) _ hp hp

lemma modulePowerTorAlgebraLimOne_isModuleComplete :
    IsModuleComplete C (algebraMap R C a) (modulePowerTorAlgebraLimOne a C M i) := by
  have hp := isModuleComplete_pi C (algebraMap R C a)
    (modulePowerTorAlgebraTower a C M i) (modulePowerTorAlgebra_isModuleComplete a C M i)
  exact isModuleComplete_coker C (algebraMap R C a)
    (M := ModuleCat.of C (∀ n, modulePowerTorAlgebraTower a C M i n))
    (N := ModuleCat.of C (∀ n, modulePowerTorAlgebraTower a C M i n)) _ hp hp

/-- Standard Tor transitions become exactly the actual C-linear quotient transitions. -/
@[reassoc] lemma modulePowerTorAlgebraComparison_transition (n : ℕ) :
    ((Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R C)).map (modulePowerReductionTransition a M n) ≫
        (torAlgebraComparison (C := C) (modulePowerReduction a M n) i).hom =
      (torAlgebraComparison (C := C) (modulePowerReduction a M (n + 1)) i).hom ≫
        (ModuleCat.restrictScalars (algebraMap R C)).map
          (modulePowerTorAlgebraTransition a C M i n) :=
  torAlgebraComparison_naturality (modulePowerReductionTransition a M n) i

/-- Compare the original standard Tor limit with the actual C-module limit. -/
def modulePowerTorAlgebraLimitComparison :
    moduleTowerLimit R
      (fun n => ((Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R C)).obj (modulePowerReduction a M n))
      (fun n => (((Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R C)).map
        (modulePowerReductionTransition a M n)).hom) ≃ₗ[R]
      (ModuleCat.restrictScalars (algebraMap R C)).obj (modulePowerTorAlgebraLimit a C M i) :=
  (moduleTowerLimitEquiv R
    (M := fun n => ((Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R C)).obj
      (modulePowerReduction a M n))
    (N := fun n => (ModuleCat.restrictScalars (algebraMap R C)).obj
      (modulePowerTorAlgebraTower a C M i n))
    (fun n => (((Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R C)).map
      (modulePowerReductionTransition a M n)).hom)
    (fun n => ((ModuleCat.restrictScalars (algebraMap R C)).map
      (modulePowerTorAlgebraTransition a C M i n)).hom)
    (fun n => (torAlgebraComparison (C := C) (modulePowerReduction a M n) i).toLinearEquiv)
    (fun n x => congrArg (fun f => f.hom x) (modulePowerTorAlgebraComparison_transition a C M i n))).trans
      (moduleTowerLimitRestrictScalarsEquiv R
        (modulePowerTorAlgebraTower a C M i) (modulePowerTorAlgebraTransition a C M i))

/-- Compare the original standard Tor difference cokernel with the actual C-module lim¹. -/
def modulePowerTorAlgebraLimOneComparison :
    ((∀ n, ((Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R C)).obj (modulePowerReduction a M n)) ⧸
      (moduleTowerDifference R
        (fun n => ((Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R C)).obj (modulePowerReduction a M n))
        (fun n => (((Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R C)).map
          (modulePowerReductionTransition a M n)).hom)).range) ≃ₗ[R]
      (ModuleCat.restrictScalars (algebraMap R C)).obj (modulePowerTorAlgebraLimOne a C M i) :=
  (moduleTowerLimOneEquiv R
    (M := fun n => ((Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R C)).obj
      (modulePowerReduction a M n))
    (N := fun n => (ModuleCat.restrictScalars (algebraMap R C)).obj
      (modulePowerTorAlgebraTower a C M i n))
    (fun n => (((Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R C)).map
      (modulePowerReductionTransition a M n)).hom)
    (fun n => ((ModuleCat.restrictScalars (algebraMap R C)).map
      (modulePowerTorAlgebraTransition a C M i n)).hom)
    (fun n => (torAlgebraComparison (C := C) (modulePowerReduction a M n) i).toLinearEquiv)
    (fun n x => congrArg (fun f => f.hom x) (modulePowerTorAlgebraComparison_transition a C M i n))).trans
      (moduleTowerLimOneRestrictScalarsEquiv R
        (modulePowerTorAlgebraTower a C M i) (modulePowerTorAlgebraTransition a C M i))

end SerrePositivity.DerivedCompletion
