module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ReflectionRing
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Closure

/-! # 標準元を保つ線形同型による反映の移送 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R]

/-- 線形同型は加群の導来完備性を保つ。 -/
theorem isModuleComplete_of_linearEquiv (f : R) (M N : ModuleCat.{u} R)
    (e : M ≃ₗ[R] N) (hM : IsModuleComplete R f M) : IsModuleComplete R f N :=
  isComplete_of_iso R f ((moduleObjectFunctor R).mapIso e.toModuleIso) hM

/-- 標準元を保つ線形同型は、完備性と加群の一意延長をまとめて移す。 -/
theorem IsCompleteModuleReflection.of_linearEquiv {k : ℕ} {a : Fin k → R}
    {B D : ModuleCat.{u} R} {b : B} {d : D}
    (h : IsCompleteModuleReflection R a B b) (e : B ≃ₗ[R] D) (he : e b = d) :
    IsCompleteModuleReflection R a D d where
  isComplete j := isModuleComplete_of_linearEquiv R (a j) B D e (h.isComplete j)
  universal N hN := by
    constructor
    · intro g q hg
      have hcomp : g.comp e.toLinearMap = q.comp e.toLinearMap :=
        (h.universal N hN).injective (by change g (e b) = q (e b); rw [he]; exact hg)
      ext x
      have hx := LinearMap.congr_fun hcomp (e.symm x)
      change g (e (e.symm x)) = q (e (e.symm x)) at hx
      simpa only [LinearEquiv.apply_symm_apply] using hx
    · intro t
      obtain ⟨g, hg⟩ := (h.universal N hN).surjective t
      refine ⟨g.comp e.symm.toLinearMap, ?_⟩
      change g (e.symm d) = t
      rw [← he, LinearEquiv.symm_apply_apply]
      exact hg

end SerrePositivity.DerivedCompletion
