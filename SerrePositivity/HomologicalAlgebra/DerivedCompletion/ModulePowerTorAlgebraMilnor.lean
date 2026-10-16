module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModulePowerTorAlgebraAlmost
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModulePowerTorComparison
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.MilnorSequence

/-! # The original power-cokernel Milnor endpoints and actual algebra-valued Tor

All comparisons retain quotient transitions and coefficient multiplication.
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits
variable {R : Type u} [CommRing R] (a : R)
  (C : Type u) [CommRing C] [Algebra R C] (M : ModuleCat.{u} R)
local notation "K₀" => CategoryTheory.Functor.obj (moduleTensorCochainFunctor
  (extRes (projectiveResolution (ModuleCat.of R C)))) M

/-- The same power-cokernel homology, now with the actual coefficient-algebra target. -/
def modulePowerCokernelTorAlgebraIso (n i : ℕ) :
    (powerCokernelComplex a K₀ n).homology (-(i : ℤ)) ≅
      (ModuleCat.restrictScalars (algebraMap R C)).obj (modulePowerTorAlgebraTower a C M i n) :=
  modulePowerCokernelTorIso a (ModuleCat.of R C) M n i ≪≫
    torAlgebraComparison (modulePowerReduction a M n) i

@[reassoc] lemma modulePowerCokernelTorAlgebraIso_transition (n i : ℕ) :
    HomologicalComplex.homologyMap (powerCokernelComplexTransition a K₀ n) (-(i : ℤ)) ≫
        (modulePowerCokernelTorAlgebraIso a C M n i).hom =
      (modulePowerCokernelTorAlgebraIso a C M (n + 1) i).hom ≫
        (ModuleCat.restrictScalars (algebraMap R C)).map
          (modulePowerTorAlgebraTransition a C M i n) := by
  simp only [modulePowerCokernelTorAlgebraIso, Iso.trans_hom]
  rw [← Category.assoc, modulePowerCokernelTorIso_transition, Category.assoc,
    modulePowerTorAlgebraComparison_transition]
  simp only [Category.assoc]

@[reassoc] lemma modulePowerCokernelTorAlgebraIso_scalar (n i : ℕ) (c : C) :
    HomologicalComplex.homologyMap (modulePowerTensorCokernelMap a M
      (extLift (projectiveResolution (ModuleCat.of R C))
        (ModuleCat.ofHom (LinearMap.mulLeft R c)) (projectiveResolution (ModuleCat.of R C))) n)
      (-(i : ℤ)) ≫ (modulePowerCokernelTorAlgebraIso a C M n i).hom =
        (modulePowerCokernelTorAlgebraIso a C M n i).hom ≫
          (ModuleCat.restrictScalars (algebraMap R C)).map
            (c • 𝟙 (modulePowerTorAlgebraTower a C M i n)) := by
  have ht := modulePowerCokernelTorIso_naturality a M
    (ModuleCat.ofHom (LinearMap.mulLeft R c)) n i
  change _ ≫ (modulePowerCokernelTorIso a (ModuleCat.of R C) M n i).hom =
    (modulePowerCokernelTorIso a (ModuleCat.of R C) M n i).hom ≫
      torCoefficientScalarEndomorphism C (modulePowerReduction a M n) i c at ht
  simp only [modulePowerCokernelTorAlgebraIso, Iso.trans_hom]
  rw [reassoc_of% ht, torAlgebraComparison_coefficient_scalar]
  simp only [Category.assoc]

/-- The actual kernel term of the original power-cokernel Milnor sequence. -/
def modulePowerCokernelTorAlgebraLimitComparison (i : ℕ) :
    moduleTowerLimit R (fun n => (powerCokernelComplex a K₀ n).homology (-(i : ℤ)))
      (fun n => (HomologicalComplex.homologyMap
        (powerCokernelComplexTransition a K₀ n) (-(i : ℤ))).hom) ≃ₗ[R]
      (ModuleCat.restrictScalars (algebraMap R C)).obj (modulePowerTorAlgebraLimit a C M i) :=
  (moduleTowerLimitEquiv R
    (M := fun n => (powerCokernelComplex a K₀ n).homology (-(i : ℤ)))
    (N := fun n => (ModuleCat.restrictScalars (algebraMap R C)).obj
      (modulePowerTorAlgebraTower a C M i n))
    (fun n => (HomologicalComplex.homologyMap
      (powerCokernelComplexTransition a K₀ n) (-(i : ℤ))).hom)
    (fun n => ((ModuleCat.restrictScalars (algebraMap R C)).map
      (modulePowerTorAlgebraTransition a C M i n)).hom)
    (fun n => (modulePowerCokernelTorAlgebraIso a C M n i).toLinearEquiv)
    (fun n x => congrArg (fun f => f.hom x)
      (modulePowerCokernelTorAlgebraIso_transition a C M n i))).trans
        (moduleTowerLimitRestrictScalarsEquiv R
          (modulePowerTorAlgebraTower a C M i) (modulePowerTorAlgebraTransition a C M i))

/-- The actual cokernel term of the original power-cokernel Milnor sequence. -/
def modulePowerCokernelTorAlgebraLimOneComparison (i : ℕ) :
    complexTowerHomologyLimOne R (powerCokernelComplex a K₀)
      (powerCokernelComplexTransition a K₀) (-(i : ℤ)) ≃ₗ[R]
      (ModuleCat.restrictScalars (algebraMap R C)).obj (modulePowerTorAlgebraLimOne a C M i) :=
  (moduleTowerLimOneEquiv R
    (M := fun n => (powerCokernelComplex a K₀ n).homology (-(i : ℤ)))
    (N := fun n => (ModuleCat.restrictScalars (algebraMap R C)).obj
      (modulePowerTorAlgebraTower a C M i n))
    (fun n => (HomologicalComplex.homologyMap
      (powerCokernelComplexTransition a K₀ n) (-(i : ℤ))).hom)
    (fun n => ((ModuleCat.restrictScalars (algebraMap R C)).map
      (modulePowerTorAlgebraTransition a C M i n)).hom)
    (fun n => (modulePowerCokernelTorAlgebraIso a C M n i).toLinearEquiv)
    (fun n x => congrArg (fun f => f.hom x)
      (modulePowerCokernelTorAlgebraIso_transition a C M n i))).trans
        (moduleTowerLimOneRestrictScalarsEquiv R
          (modulePowerTorAlgebraTower a C M i) (modulePowerTorAlgebraTransition a C M i))

@[simp] lemma modulePowerCokernelTorAlgebraLimitComparison_apply (i : ℕ)
    (x : moduleTowerLimit R (fun n => (powerCokernelComplex a K₀ n).homology (-(i : ℤ)))
      (fun n => (HomologicalComplex.homologyMap
        (powerCokernelComplexTransition a K₀ n) (-(i : ℤ))).hom)) (n : ℕ) :
    (modulePowerCokernelTorAlgebraLimitComparison a C M i x).val n =
      (modulePowerCokernelTorAlgebraIso a C M n i).hom (x.val n) := rfl

@[simp] lemma modulePowerCokernelTorAlgebraLimOneComparison_mk (i : ℕ)
    (x : ∀ n, (powerCokernelComplex a K₀ n).homology (-(i : ℤ))) :
    modulePowerCokernelTorAlgebraLimOneComparison a C M i (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (fun n => (modulePowerCokernelTorAlgebraIso a C M n i).hom (x n)) := rfl

end SerrePositivity.DerivedCompletion
