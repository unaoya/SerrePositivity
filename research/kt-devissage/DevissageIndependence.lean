module
public import SerrePositivity.KTheory.DevissageExact

/-! # Independence of annihilated-factor filtrations -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory Limits
variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- The canonical short exact sequence for a submodule of a finite module. -/
def finiteSubmoduleShortExact (M : ModuleCat.{u} R) [Module.Finite R M]
    (U : Submodule R M) :
    SupportedModuleShortExact (⊤ : TopologicalSpace.Closeds (PrimeSpectrum R)) where
  left := wholeSupportedModule (ModuleCat.of R U)
  middle := wholeSupportedModule M
  right := wholeSupportedModule (ModuleCat.of R (M ⧸ U))
  f := U.subtype
  g := U.mkQ
  injective := Subtype.val_injective
  exact := LinearMap.exact_iff.mpr (by rw [Submodule.ker_mkQ, Submodule.range_subtype])
  surjective := U.mkQ_surjective

/-- On an annihilated module, every filtration has the module's own quotient-ring class. -/
lemma DevissageFlag.value_of_annihilated {J : Ideal R} {M : ModuleCat.{u} R}
    (F : DevissageFlag J M) : ∀ [Module.Finite R M]
      (h : J ≤ Module.annihilator R M), F.value = annihilatedClass J M h := by
  induction F with
  | @zero M hz =>
    intro _ h
    exact (annihilatedClass_of_isZero J M h hz).symm
  | @step M U h rest ih =>
    intro _ hM
    let E := finiteSubmoduleShortExact M U
    have hU := annihilator_le_of_injective J E.f E.injective hM
    have hQ := annihilator_le_of_surjective J E.g E.surjective hM
    have ha := annihilatedClass_shortExact J E hU hM hQ
    change annihilatedClass J M hM =
      annihilatedClass J (ModuleCat.of R U) hU +
        annihilatedClass J (ModuleCat.of R (M ⧸ U)) hQ at ha
    change rest.value + annihilatedClass J (ModuleCat.of R (M ⧸ U)) h = _
    rw [ih hU]
    exact ha.symm

/-- A zero module gives zero for every annihilated-factor filtration. -/
lemma DevissageFlag.value_of_isZero {J : Ideal R} {M : ModuleCat.{u} R}
    (F : DevissageFlag J M) [Module.Finite R M] (hz : IsZero M) : F.value = 0 := by
  have : Subsingleton M := ModuleCat.subsingleton_of_isZero hz
  have h : J ≤ Module.annihilator R M := by
    intro r hr
    rw [Module.mem_annihilator]
    intro m
    exact Subsingleton.elim _ _
  rw [F.value_of_annihilated h, annihilatedClass_of_isZero J M h hz]

/-- Filtration values are independent of all choices of submodules and annihilating powers. -/
lemma DevissageFlag.value_eq {J : Ideal R} {M : ModuleCat.{u} R}
    (G : DevissageFlag J M) : ∀ [Module.Finite R M] (F : DevissageFlag J M),
      F.value = G.value := by
  induction G with
  | @zero M hz =>
    intro _ F
    exact F.value_of_isZero hz
  | @step M U h rest ih =>
    intro _ F
    let E := finiteSubmoduleShortExact M U
    obtain ⟨FL, FQ, he⟩ := F.exists_restriction E.f E.g E.injective E.exact E.surjective
    change F.value = rest.value + annihilatedClass J (ModuleCat.of R (M ⧸ U)) h
    rw [he, ih FL, FQ.value_of_annihilated h]
    rfl

end SerrePositivity
