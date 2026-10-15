module
public import SerrePositivity.KTheory.SupportedExactEuler
public import SerrePositivity.KTheory.ResolutionAdditivity
public import Mathlib.Algebra.Homology.HomotopyCategory.HomologicalFunctor
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence

/-! # Homology Euler classes from supported K₀ to supported G₀ -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory Limits Pretriangulated
variable {R : Type u} [CommRing R] [IsNoetherianRing R]
  (Z : TopologicalSpace.Closeds (PrimeSpectrum R))

/-- Forget support and perfectness to obtain the ambient homotopy object. -/
abbrev supportedPerfectAmbient : SupportedPerfectHomotopyOn Z ⥤
    HomotopyCategory (ModuleCat.{u} R) (.up ℤ) :=
  supportedPerfectOnInclusion Z ⋙ perfectHomotopyInclusion R

lemma supportedPerfectHomology_finite (X : SupportedPerfectHomotopyOn Z) (q : ℤ) :
    Module.Finite R ((HomotopyCategory.homologyFunctor (ModuleCat.{u} R) (.up ℤ) q).obj
      X.obj.obj) := by
  obtain ⟨P : CochainComplex (ModuleCat.{u} R) ℤ, hP⟩ := X.obj.obj.quotient_obj_surjective
  have hp : strictlyPerfectComplex R P := by
    apply (perfectHomotopyProperty_quotient R P).mp
    rw [hP]
    exact X.obj.property
  have := (hp.2 q).1
  have : Module.Finite R (P.homology q) := homology_moduleFinite P q
  have : Module.Finite R ((HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℤ) q).obj P) :=
    by change Module.Finite R (P.homology q); infer_instance
  rw [← hP]
  exact Module.Finite.of_surjective
    ((HomotopyCategory.homologyFunctorFactors _ _ q).app P).inv.hom
    ((HomotopyCategory.homologyFunctorFactors _ _ q).app P).toLinearEquiv.symm.surjective

/-- Homology, bundled as a finite supported module. -/
def supportedPerfectHomology (X : SupportedPerfectHomotopyOn Z) (q : ℤ) : SupportedFGModuleOn Z :=
  ⟨(HomotopyCategory.homologyFunctor (ModuleCat.{u} R) (.up ℤ) q).obj X.obj.obj,
    supportedPerfectHomology_finite Z X q, X.property q⟩

lemma supportedPerfectHomology_bounded (X : SupportedPerfectHomotopyOn Z) :
    ∃ a b : ℤ, ∀ q, q < a ∨ b < q → IsZero (supportedPerfectHomology Z X q).obj := by
  obtain ⟨P : CochainComplex (ModuleCat.{u} R) ℤ, hP⟩ := X.obj.obj.quotient_obj_surjective
  have hp : strictlyPerfectComplex R P := by
    apply (perfectHomotopyProperty_quotient R P).mp
    rw [hP]
    exact X.obj.property
  obtain ⟨a, b, ha, hb⟩ := hp.1
  refine ⟨a, b, fun q hq => ?_⟩
  have hz : IsZero (P.X q) := hq.elim (fun h => P.isZero_of_isStrictlyGE a q h)
    (fun h => P.isZero_of_isStrictlyLE b q h)
  have hh := isZero_homology_of_isZero_X P q hz
  change IsZero ((HomotopyCategory.homologyFunctor _ _ q).obj X.obj.obj)
  rw [← hP]
  exact hh.of_iso ((HomotopyCategory.homologyFunctorFactors _ _ q).app P)

/-- The finite homology Euler sum of a perfect supported object. -/
def supportedHomologyEuler (X : SupportedPerfectHomotopyOn Z) : G0WithSupport Z :=
  supportedModuleEuler (supportedPerfectHomology Z X)

lemma supportedHomologyEuler_iso {X Y : SupportedPerfectHomotopyOn Z} (e : X ≅ Y) :
    supportedHomologyEuler Z X = supportedHomologyEuler Z Y := by
  unfold supportedHomologyEuler supportedModuleEuler
  congr 1
  funext q
  have h : G0WithSupport.mk (supportedPerfectHomology Z X q) =
      G0WithSupport.mk (supportedPerfectHomology Z Y q) := by
    apply G0WithSupport.mk_iso
    exact (HomotopyCategory.homologyFunctor _ _ q).mapIso
      ((supportedPerfectAmbient Z).mapIso e)
  rw [h]

lemma supportedHomologyEuler_triangle (T : Triangle (SupportedPerfectHomotopyOn Z))
    (hT : T ∈ distTriang _) :
    supportedHomologyEuler Z T.obj₂ =
      supportedHomologyEuler Z T.obj₁ + supportedHomologyEuler Z T.obj₃ := by
  let I := supportedPerfectAmbient Z
  let t := I.mapTriangle.obj T
  have ht : t ∈ distTriang _ := I.map_distinguished T hT
  let F := HomotopyCategory.homologyFunctor (ModuleCat.{u} R) (.up ℤ) 0
  apply supportedModuleEuler_exact_sequence
    (supportedPerfectHomology Z T.obj₁) (supportedPerfectHomology Z T.obj₂)
    (supportedPerfectHomology Z T.obj₃)
    (fun q => (F.shift q).map t.mor₁) (fun q => (F.shift q).map t.mor₂)
    (fun q => F.homologySequenceδ t q (q + 1) rfl)
  · intro q
    exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      (F.homologySequence_exact₂ t ht q)
  · intro q
    exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      (F.homologySequence_exact₃ t ht q (q + 1) rfl)
  · intro q
    exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      (F.homologySequence_exact₁ t ht q (q + 1) rfl)
  · exact supportedPerfectHomology_bounded Z T.obj₂
  · exact supportedPerfectHomology_bounded Z T.obj₃

namespace K0WithSupport
/-- Euler evaluation by finite homology classes. -/
def homologyEuler : K0WithSupport Z →+ G0WithSupport Z :=
  lift Z (supportedHomologyEuler Z) (supportedHomologyEuler_iso Z)
    (supportedHomologyEuler_triangle Z)

@[simp] lemma homologyEuler_mk (X : SupportedPerfectHomotopyOn Z) :
    homologyEuler Z (mk Z X) = supportedHomologyEuler Z X := by
  unfold homologyEuler
  exact lift_mk ..

lemma homologyEuler_resolution (M : SupportedFGModuleOn Z) (F : PerfectModuleResolution M.obj) :
    homologyEuler Z (F.k0Class Z M.property.2) = G0WithSupport.mk M := by
  rw [PerfectModuleResolution.k0Class, homologyEuler_mk]
  unfold supportedHomologyEuler supportedModuleEuler
  rw [finsum_eq_single _ (0 : ℤ)]
  · simp only [Int.negOnePow_zero, Units.val_one, one_smul]
    apply G0WithSupport.mk_iso
    exact (HomotopyCategory.homologyFunctorFactors _ _ 0).app F.complex ≪≫
      F.resolution.homologyZeroIso
  · intro q hq
    rw [G0WithSupport.mk_of_isZero _ ?_, smul_zero]
    exact (F.resolution.isZero_homology q hq).of_iso
      ((HomotopyCategory.homologyFunctorFactors _ _ q).app F.complex)

variable [HasFiniteProjectiveResolutions R]
lemma homologyEuler_resolutionMap : (homologyEuler Z).comp (G0WithSupport.resolutionMap Z) =
    AddMonoidHom.id (G0WithSupport Z) := by
  apply G0WithSupport.hom_ext
  intro M
  simp only [AddMonoidHom.comp_apply, G0WithSupport.resolutionMap_mk, AddMonoidHom.id_apply]
  exact homologyEuler_resolution Z M (chosenPerfectModuleResolution M.obj)
end K0WithSupport
end SerrePositivity
