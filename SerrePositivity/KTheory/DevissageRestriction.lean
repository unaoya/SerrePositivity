module
public import SerrePositivity.KTheory.DevissageInverse

/-! # Restriction of scalars from a quotient ring to its closed support -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory Limits
open scoped ModuleCat.Algebra
variable {R : Type u} [CommRing R] (J : Ideal R)

/-- A quotient-ring module has annihilator containing J after restriction. -/
lemma quotientModule_annihilator (M : ModuleCat.{u} (R ⧸ J)) :
    J ≤ Module.annihilator R M := by
  intro r hr
  rw [Module.mem_annihilator]
  intro m
  change Ideal.Quotient.mk J r • m = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hr, zero_smul]

/-- Restriction of a finite quotient-ring module is finite and supported on V(J). -/
def quotientSupportedModule (M : SupportedFGModuleOn
    (⊤ : TopologicalSpace.Closeds (PrimeSpectrum (R ⧸ J)))) :
    SupportedFGModuleOn (supportZeroLocus J) := by
  have := M.property.1
  have : Module.Finite R M.obj := Module.Finite.trans (R ⧸ J) M.obj
  refine ⟨ModuleCat.of R M.obj, inferInstance, ?_⟩
  intro p hp
  exact (quotientModule_annihilator J M.obj).trans (Module.mem_support_iff_of_finite.mp hp)

/-- Restriction preserves short exact sequences of finite quotient-ring modules. -/
def quotientSupportedShortExact (E : SupportedModuleShortExact
    (⊤ : TopologicalSpace.Closeds (PrimeSpectrum (R ⧸ J)))) :
    SupportedModuleShortExact (supportZeroLocus J) where
  left := quotientSupportedModule J E.left
  middle := quotientSupportedModule J E.middle
  right := quotientSupportedModule J E.right
  f := E.f.restrictScalars R
  g := E.g.restrictScalars R
  injective := E.injective
  exact := E.exact
  surjective := E.surjective

/-- Isomorphisms remain isomorphisms on restriction of scalars. -/
def quotientSupportedIso {M N : SupportedFGModuleOn
    (⊤ : TopologicalSpace.Closeds (PrimeSpectrum (R ⧸ J)))} (e : M.obj ≅ N.obj) :
    (quotientSupportedModule J M).obj ≅ (quotientSupportedModule J N).obj :=
  (e.toLinearEquiv.restrictScalars R).toModuleIso

/-- Restriction of scalars gives the forward dévissage homomorphism. -/
def quotientG0ToSupported : G0 (R ⧸ J) →+ G0WithSupport (supportZeroLocus J) :=
  G0WithSupport.lift (fun M => G0WithSupport.mk (quotientSupportedModule J M))
    (fun e => G0WithSupport.mk_iso (quotientSupportedIso J e))
    (fun E => G0WithSupport.mk_shortExact (quotientSupportedShortExact J E))

@[simp] lemma quotientG0ToSupported_mk (M : SupportedFGModuleOn
    (⊤ : TopologicalSpace.Closeds (PrimeSpectrum (R ⧸ J)))) :
    quotientG0ToSupported J (G0WithSupport.mk M) =
      G0WithSupport.mk (quotientSupportedModule J M) := by
  simp [quotientG0ToSupported]

/-- Restriction recovers an annihilated module with its original R-action. -/
def annihilatedRestrictionIso (M : ModuleCat.{u} R) [Module.Finite R M]
    (h : J ≤ Module.annihilator R M) :
    (quotientSupportedModule J (annihilatedFGModule J M h)).obj ≅ M :=
  (show (quotientSupportedModule J (annihilatedFGModule J M h)).obj ≃ₗ[R] M from
    { toFun := id
      invFun := id
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }).toModuleIso

lemma quotientG0ToSupported_annihilatedClass
    (M : SupportedFGModuleOn (supportZeroLocus J)) (h : J ≤ Module.annihilator R M.obj) :
    quotientG0ToSupported J (by have := M.property.1; exact annihilatedClass J M.obj h) =
      G0WithSupport.mk M := by
  have := M.property.1
  change quotientG0ToSupported J (G0WithSupport.mk (annihilatedFGModule J M.obj h)) = _
  rw [quotientG0ToSupported_mk]
  exact G0WithSupport.mk_iso (annihilatedRestrictionIso J M.obj h)

/-- The quotient action obtained from the annihilator is the original quotient-ring action. -/
def quotientAnnihilatedIso (M : SupportedFGModuleOn
    (⊤ : TopologicalSpace.Closeds (PrimeSpectrum (R ⧸ J)))) :
    (annihilatedFGModule J (quotientSupportedModule J M).obj
      (quotientModule_annihilator J M.obj)).obj ≅ M.obj := by
  have := (quotientSupportedModule J M).property.1
  let A := annihilatedFGModule J (quotientSupportedModule J M).obj
    (quotientModule_annihilator J M.obj)
  let e : A.obj ≃ₗ[R ⧸ J] M.obj :=
    { toFun := id
      invFun := id
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun q m => by
        refine Quotient.inductionOn' q ?_
        intro r
        rfl }
  exact e.toModuleIso
end SerrePositivity
