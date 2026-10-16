module
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionH0Comparison
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionH0Algebra
public import Mathlib.Algebra.Algebra.Bilinear

/-! # Algebra universality of actual completion H⁰ on nonpositive sources -/
@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard
section LinearExtension
variable (R B C T : Type*) [CommRing R] [CommRing B] [CommRing C] [CommRing T]
    [Algebra R B] [Algebra R C] [Algebra R T]
/-- A linearly dense algebra unit makes every compatible linear extension multiplicative. -/
def algHomOfDenseLinearExtension (j : B →ₐ[R] C) (f : B →ₐ[R] T) (g : C →ₗ[R] T)
    (hg : ∀ b, g (j b) = f b)
    (hd : Function.Injective (fun l : C →ₗ[R] T => l.comp j.toLinearMap)) : C →ₐ[R] T := by
  apply AlgHom.ofLinearMap g
  · simpa only [map_one] using hg 1
  · intro x y
    have hleft (b : B) : g.comp (LinearMap.mulLeft R (j b)) =
        (LinearMap.mulLeft R (f b)).comp g := by
      apply hd
      apply LinearMap.ext
      intro z
      change g (j b * j z) = f b * g (j z)
      rw [← map_mul j, hg, hg, map_mul f]
    have hright (y : C) : g.comp (LinearMap.mulRight R y) =
        (LinearMap.mulRight R (g y)).comp g := by
      apply hd
      apply LinearMap.ext
      intro b
      change g (j b * y) = g (j b) * g y
      rw [hg]
      exact LinearMap.congr_fun (hleft b) y
    exact LinearMap.congr_fun (hright y) x
end LinearExtension
variable (R : Type u) [CommRing R] (a : R)
    (A : CommMon (DerivedCategory.Minus (ModuleCat.{u} R))) [A.X.obj.IsLE 0]
    (T : Type u) [CommRing T] [Algebra R T]
    (hT : IsModuleComplete R a (ModuleCat.of R T))
set_option quotPrecheck false in
local notation "H" => (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj A.X.obj
set_option quotPrecheck false in
local notation "HC" => (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
  ((boundedAboveCompletionCommMonFunctor R a).obj A).X.obj
local notation "J" => derivedH0AlgMap (boundedAboveCompletionAlgebraUnit R a A)

include hT in
/-- Linear maps out of actual completed H⁰ are determined by the original algebra unit. -/
theorem completionH0_linear_ext :
    letI := derivedH0CommRing A
    letI := derivedH0Algebra A
    letI := derivedH0CommRing ((boundedAboveCompletionCommMonFunctor R a).obj A)
    letI := derivedH0Algebra ((boundedAboveCompletionCommMonFunctor R a).obj A)
    Function.Injective (fun g : HC →ₗ[R] T => g.comp (J).toLinearMap) := by
  let := derivedH0CommRing A
  let := derivedH0Algebra A
  let := derivedH0CommRing ((boundedAboveCompletionCommMonFunctor R a).obj A)
  let := derivedH0Algebra ((boundedAboveCompletionCommMonFunctor R a).obj A)
  intro g k hg
  have he : completionH0HomEquiv R a A.X.obj (ModuleCat.of R T) hT (ModuleCat.ofHom g) =
      completionH0HomEquiv R a A.X.obj (ModuleCat.of R T) hT (ModuleCat.ofHom k) := by
    rw [completionH0HomEquiv_apply, completionH0HomEquiv_apply]
    ext x
    have hx := LinearMap.congr_fun hg x
    change g ((DerivedCategory.homologyFunctor (ModuleCat R) 0).map
      ((derivedComplexCompletionUnit R a).app A.X.obj) x) =
      k ((DerivedCategory.homologyFunctor (ModuleCat R) 0).map
        ((derivedComplexCompletionUnit R a).app A.X.obj) x)
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply,
      completionH0AlgebraUnit_apply, boundedAboveDerivedCompletionUnit,
      ObjectProperty.homMk] at hx
    exact hx
  exact congrArg (fun f => f.hom) ((completionH0HomEquiv R a A.X.obj
    (ModuleCat.of R T) hT).injective he)

/-- Extend an algebra map across the original actual H⁰ completion unit. -/
def completionH0AlgebraLift :
    letI := derivedH0CommRing A
    letI := derivedH0Algebra A
    letI := derivedH0CommRing ((boundedAboveCompletionCommMonFunctor R a).obj A)
    letI := derivedH0Algebra ((boundedAboveCompletionCommMonFunctor R a).obj A)
    (H →ₐ[R] T) → (HC →ₐ[R] T) := by
  letI := derivedH0CommRing A
  letI := derivedH0Algebra A
  letI := derivedH0CommRing ((boundedAboveCompletionCommMonFunctor R a).obj A)
  letI := derivedH0Algebra ((boundedAboveCompletionCommMonFunctor R a).obj A)
  intro f
  let g := (completionH0HomEquiv R a A.X.obj (ModuleCat.of R T) hT).symm
    (ModuleCat.ofHom f.toLinearMap)
  have hg (x : H) : g.hom (J x) = f x := by
    have he := (completionH0HomEquiv R a A.X.obj (ModuleCat.of R T) hT).apply_symm_apply
      (ModuleCat.ofHom f.toLinearMap)
    rw [completionH0HomEquiv_apply] at he
    have hx := congrArg (fun l => l.hom x) he
    change g.hom ((DerivedCategory.homologyFunctor (ModuleCat R) 0).map
      ((derivedComplexCompletionUnit R a).app A.X.obj) x) = f x at hx
    rw [completionH0AlgebraUnit_apply]
    exact hx
  exact algHomOfDenseLinearExtension R H HC T J f g.hom hg
    (completionH0_linear_ext R a A T hT)

/-- The extension retains the original completion-unit diagram. -/
lemma completionH0AlgebraLift_unit :
    letI := derivedH0CommRing A
    letI := derivedH0Algebra A
    letI := derivedH0CommRing ((boundedAboveCompletionCommMonFunctor R a).obj A)
    letI := derivedH0Algebra ((boundedAboveCompletionCommMonFunctor R a).obj A)
    ∀ (f : H →ₐ[R] T), (completionH0AlgebraLift R a A T hT f).comp J = f := by
  let := derivedH0CommRing A
  let := derivedH0Algebra A
  let := derivedH0CommRing ((boundedAboveCompletionCommMonFunctor R a).obj A)
  let := derivedH0Algebra ((boundedAboveCompletionCommMonFunctor R a).obj A)
  intro f
  ext x
  have he := (completionH0HomEquiv R a A.X.obj (ModuleCat.of R T) hT).apply_symm_apply
    (ModuleCat.ofHom f.toLinearMap)
  rw [completionH0HomEquiv_apply] at he
  have hx := congrArg (fun l => l.hom x) he
  change ((completionH0HomEquiv R a A.X.obj (ModuleCat.of R T) hT).symm
    (ModuleCat.ofHom f.toLinearMap)).hom (J x) = f x
  rw [completionH0AlgebraUnit_apply]
  exact hx

include hT in
/-- Actual completed H⁰ is universal as an algebra, not merely as a module. -/
theorem completionH0_existsUnique_algHom :
    letI := derivedH0CommRing A
    letI := derivedH0Algebra A
    letI := derivedH0CommRing ((boundedAboveCompletionCommMonFunctor R a).obj A)
    letI := derivedH0Algebra ((boundedAboveCompletionCommMonFunctor R a).obj A)
    ∀ (f : H →ₐ[R] T), ∃! g : HC →ₐ[R] T, g.comp J = f := by
  let := derivedH0CommRing A
  let := derivedH0Algebra A
  let := derivedH0CommRing ((boundedAboveCompletionCommMonFunctor R a).obj A)
  let := derivedH0Algebra ((boundedAboveCompletionCommMonFunctor R a).obj A)
  intro f
  refine ⟨completionH0AlgebraLift R a A T hT f, completionH0AlgebraLift_unit R a A T hT f, ?_⟩
  intro g hg
  apply AlgHom.toLinearMap_injective
  apply completionH0_linear_ext R a A T hT
  exact congrArg AlgHom.toLinearMap (hg.trans
    (completionH0AlgebraLift_unit R a A T hT f).symm)

end SerrePositivity.DerivedCompletion
