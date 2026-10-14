module
public import SerrePositivity.KTheory.DevissageIndependence

/-! # The inverse of restriction of scalars in supported G₀ dévissage -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory Limits
variable {R : Type u} [CommRing R] [IsNoetherianRing R] (J : Ideal R)

/-- Isomorphic finite modules have equal values for any annihilated-factor filtrations. -/
lemma DevissageFlag.value_iso {M N : ModuleCat.{u} R}
    [Module.Finite R M] [Module.Finite R N]
    (F : DevissageFlag J M) (G : DevissageFlag J N) (e : M ≅ N) : F.value = G.value := by
  let O := ModuleCat.of R PUnit
  let g : M →ₗ[R] O := 0
  have he : Function.Exact e.inv.hom g := by
    intro m
    constructor
    · intro _
      exact ⟨e.hom m, ConcreteCategory.congr_hom e.hom_inv_id m⟩
    · intro _
      rfl
  have hf : Function.Injective e.inv.hom := e.toLinearEquiv.symm.injective
  have hg : Function.Surjective g := fun x => ⟨0, Subsingleton.elim _ _⟩
  obtain ⟨FN, FO, h⟩ := F.exists_restriction e.inv.hom g hf he hg
  rw [h, G.value_eq FN, FO.value_of_isZero (ModuleCat.isZero_of_subsingleton O), add_zero]

/-- Choose a finite annihilated-factor filtration of a supported finite module. -/
def chosenDevissageFlag (M : SupportedFGModuleOn (supportZeroLocus J)) : DevissageFlag J M.obj :=
  Classical.choice (by
    have := M.property.1
    exact exists_devissageFlag J M.obj M.property.2)

/-- The class obtained by summing annihilated factors in the quotient ring. -/
def devissageClass (M : SupportedFGModuleOn (supportZeroLocus J)) : G0 (R ⧸ J) := by
  have := M.property.1
  exact (chosenDevissageFlag J M).value

lemma devissageClass_eq (M : SupportedFGModuleOn (supportZeroLocus J))
    (F : DevissageFlag J M.obj) :
    devissageClass J M = (by have := M.property.1; exact F.value) := by
  have := M.property.1
  exact F.value_eq (chosenDevissageFlag J M)

lemma devissageClass_iso {M N : SupportedFGModuleOn (supportZeroLocus J)} (e : M.obj ≅ N.obj) :
    devissageClass J M = devissageClass J N := by
  have := M.property.1
  have := N.property.1
  exact (chosenDevissageFlag J M).value_iso J (chosenDevissageFlag J N) e

lemma devissageClass_shortExact (E : SupportedModuleShortExact (supportZeroLocus J)) :
    devissageClass J E.middle = devissageClass J E.left + devissageClass J E.right := by
  have := E.left.property.1
  have := E.middle.property.1
  have := E.right.property.1
  obtain ⟨FL, FR, h⟩ := (chosenDevissageFlag J E.middle).exists_restriction
    E.f E.g E.injective E.exact E.surjective
  rw [devissageClass_eq J E.left FL, devissageClass_eq J E.right FR]
  exact h

/-- Dévissage from modules supported in V(J) to modules over R/J. -/
def devissageInverse : G0WithSupport (supportZeroLocus J) →+ G0 (R ⧸ J) :=
  G0WithSupport.lift (devissageClass J) (fun e => devissageClass_iso J e)
    (devissageClass_shortExact J)

@[simp] lemma devissageInverse_mk (M : SupportedFGModuleOn (supportZeroLocus J)) :
    devissageInverse J (G0WithSupport.mk M) = devissageClass J M :=
  by simp [devissageInverse]
end SerrePositivity
