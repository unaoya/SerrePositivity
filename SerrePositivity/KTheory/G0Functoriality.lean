module
public import SerrePositivity.KTheory.G0Supported
public import SerrePositivity.HomologicalAlgebra.BaseChange
public import SerrePositivity.CommutativeAlgebra.Support.Closed
public import Mathlib.Algebra.Category.ModuleCat.Descent
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Localization.BaseChange

/-! # Support enlargement and flat base change on supported G₀ -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory Limits
open scoped TensorProduct
variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]

/-- A finite module's support pulls back under extension of scalars. -/
lemma moduleSupport_extendScalars (φ : R →+* S) (M : ModuleCat.{u} R)
    [Module.Finite R M] :
    Module.support S ((ModuleCat.extendScalars φ).obj M) ⊆
      (PrimeSpectrum.comap φ) ⁻¹' Module.support R M := by
  algebraize [φ]
  have : Module.Finite S ((ModuleCat.extendScalars φ).obj M) := by
    change Module.Finite S (S ⊗[R] M)
    infer_instance
  intro p hp
  apply Module.mem_support_iff_of_finite.mpr
  intro r hr
  change φ r ∈ p.asIdeal
  apply (Module.mem_support_iff_of_finite.mp hp)
  rw [Module.mem_annihilator]
  change ∀ x : S ⊗[R] M, φ r • x = 0
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul s m =>
    have hm : r • m = 0 := Module.mem_annihilator.mp hr m
    simpa [TensorProduct.smul_tmul', Algebra.smul_def, RingHom.algebraMap_toAlgebra, mul_comm] using
      congrArg (fun m => s ⊗ₜ[R] m) hm
  | add x y hx hy => simp [smul_add, hx, hy]


/-- The fraction model and tensor model of module localization agree. -/
def localizedModuleTensorEquiv (P : Submonoid R) (M : ModuleCat.{u} R) :
    LocalizedModule P M ≃ₗ[Localization P] Localization P ⊗[R] M :=
  LocalizedModule.equivTensorProduct P M

namespace SupportedFGModuleOn
variable {Z W : TopologicalSpace.Closeds (PrimeSpectrum R)}
/-- Enlarge the closed support of a finite module. -/
abbrev enlarge (h : Z ≤ W) (M : SupportedFGModuleOn Z) : SupportedFGModuleOn W :=
  ⟨M.obj, M.property.mono h⟩

/-- Flatness is unnecessary for object-level base change. -/
abbrev baseChange (φ : R →+* S) (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (W : TopologicalSpace.Closeds (PrimeSpectrum S)) (h : supportPullback φ Z ≤ W)
    (M : SupportedFGModuleOn Z) : SupportedFGModuleOn W :=
  ⟨(ModuleCat.extendScalars φ).obj M.obj, by
    algebraize [φ]
    refine ⟨?_, (moduleSupport_extendScalars φ M.obj).trans ?_⟩
    · change Module.Finite S (S ⊗[R] M.obj)
      infer_instance
    · intro p hp
      exact h (M.property.2 hp)⟩
end SupportedFGModuleOn

namespace SupportedModuleShortExact
variable {Z W : TopologicalSpace.Closeds (PrimeSpectrum R)}
def enlarge (h : Z ≤ W) (E : SupportedModuleShortExact Z) : SupportedModuleShortExact W where
  left := E.left.enlarge h
  middle := E.middle.enlarge h
  right := E.right.enlarge h
  f := E.f
  g := E.g
  injective := E.injective
  exact := E.exact
  surjective := E.surjective

/-- The ambient short complex associated to the linear exactness certificate. -/
def shortComplex (E : SupportedModuleShortExact Z) : ShortComplex (ModuleCat.{u} R) :=
  ModuleCat.shortComplexOfCompEqZero E.f E.g
    (LinearMap.ext fun x => E.exact.apply_apply_eq_zero x)

lemma shortComplex_shortExact (E : SupportedModuleShortExact Z) :
    E.shortComplex.ShortExact :=
  ModuleCat.shortComplex_shortExact _ E.exact E.injective E.surjective


/-- Flat base change preserves the ambient short exact sequence. -/
def baseChange (φ : R →+* S) (hf : φ.Flat)
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (W : TopologicalSpace.Closeds (PrimeSpectrum S)) (h : supportPullback φ Z ≤ W)
    (E : SupportedModuleShortExact Z) : SupportedModuleShortExact W := by
  have : PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} φ) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  have hs := E.shortComplex_shortExact.map_of_exact (ModuleCat.extendScalars φ)
  exact
    { left := E.left.baseChange φ Z W h
      middle := E.middle.baseChange φ Z W h
      right := E.right.baseChange φ Z W h
      f := ((ModuleCat.extendScalars φ).map (ModuleCat.ofHom E.f)).hom
      g := ((ModuleCat.extendScalars φ).map (ModuleCat.ofHom E.g)).hom
      injective := (ModuleCat.mono_iff_injective _).mp hs.mono_f
      exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hs.exact
      surjective := (ModuleCat.epi_iff_surjective _).mp hs.epi_g }

end SupportedModuleShortExact

namespace G0WithSupport
variable {Z W V : TopologicalSpace.Closeds (PrimeSpectrum R)}
/-- Support enlargement on Grothendieck groups. -/
def enlarge (h : Z ≤ W) : G0WithSupport Z →+ G0WithSupport W :=
  lift (fun M => mk (M.enlarge h)) (fun e => mk_iso e)
    (fun E => mk_shortExact (E.enlarge h))

@[simp] lemma enlarge_mk (h : Z ≤ W) (M : SupportedFGModuleOn Z) :
    enlarge h (mk M) = mk (M.enlarge h) := lift_mk ..

@[simp] lemma enlarge_refl : enlarge (le_refl Z) = AddMonoidHom.id (G0WithSupport Z) := by
  apply hom_ext
  intro M
  simp [SupportedFGModuleOn.enlarge]

lemma enlarge_comp (hZW : Z ≤ W) (hWV : W ≤ V) :
    (enlarge hWV).comp (enlarge hZW) = enlarge (hZW.trans hWV) := by
  apply hom_ext
  intro M
  simp

/-- Flat extension of scalars on Grothendieck groups. -/
def map (φ : R →+* S) (hf : φ.Flat)
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (W : TopologicalSpace.Closeds (PrimeSpectrum S)) (h : supportPullback φ Z ≤ W) :
    G0WithSupport Z →+ G0WithSupport W :=
  lift (fun M => mk (M.baseChange φ Z W h))
    (fun e => mk_iso ((ModuleCat.extendScalars φ).mapIso e))
    (fun E => mk_shortExact (E.baseChange φ hf Z W h))

@[simp] lemma map_mk (φ : R →+* S) (hf : φ.Flat)
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (W : TopologicalSpace.Closeds (PrimeSpectrum S)) (h : supportPullback φ Z ≤ W)
    (M : SupportedFGModuleOn Z) :
    map φ hf Z W h (mk M) = mk (M.baseChange φ Z W h) := lift_mk ..

lemma map_id (h : supportPullback (RingHom.id R) Z ≤ Z) :
    map (RingHom.id R) (RingHom.Flat.id R) Z Z h = AddMonoidHom.id (G0WithSupport Z) := by
  apply hom_ext
  intro M
  simpa using mk_iso ((ModuleCat.extendScalarsId R).app M.obj)

lemma map_comp (φ : R →+* S) (hf : φ.Flat) (ψ : S →+* T) (hg : ψ.Flat)
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (W : TopologicalSpace.Closeds (PrimeSpectrum S))
    (V : TopologicalSpace.Closeds (PrimeSpectrum T))
    (hφ : supportPullback φ Z ≤ W) (hψ : supportPullback ψ W ≤ V)
    (hcomp : supportPullback (ψ.comp φ) Z ≤ V) :
    (map ψ hg W V hψ).comp (map φ hf Z W hφ) =
      map (ψ.comp φ) (hf.comp hg) Z V hcomp := by
  apply hom_ext
  intro M
  simpa using mk_iso ((ModuleCat.extendScalarsComp φ ψ).symm.app M.obj)

lemma enlarge_map (φ : R →+* S) (hf : φ.Flat)
    (Z Z' : TopologicalSpace.Closeds (PrimeSpectrum R))
    (W W' : TopologicalSpace.Closeds (PrimeSpectrum S))
    (hZ : Z ≤ Z') (hW : W ≤ W')
    (h : supportPullback φ Z ≤ W) (h' : supportPullback φ Z' ≤ W') :
    (enlarge hW).comp (map φ hf Z W h) = (map φ hf Z' W' h').comp (enlarge hZ) := by
  apply hom_ext
  intro M
  simp

/-- Supported localization into any chosen localization algebra. -/
def localize (P : Submonoid R) [Algebra R S] [IsLocalization P S]
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (W : TopologicalSpace.Closeds (PrimeSpectrum S))
    (h : supportPullback (algebraMap R S) Z ≤ W) : G0WithSupport Z →+ G0WithSupport W :=
  map (algebraMap R S)
    (by rw [RingHom.flat_algebraMap_iff]; exact IsLocalization.flat S P) Z W h

@[simp] lemma localize_mk (P : Submonoid R) [Algebra R S] [IsLocalization P S]
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (W : TopologicalSpace.Closeds (PrimeSpectrum S))
    (h : supportPullback (algebraMap R S) Z ≤ W) (M : SupportedFGModuleOn Z) :
    localize P Z W h (mk M) = mk (M.baseChange (algebraMap R S) Z W h) := map_mk ..

end G0WithSupport

end SerrePositivity
