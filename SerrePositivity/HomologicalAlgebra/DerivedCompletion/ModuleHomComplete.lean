module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleClosure
public import Mathlib.Algebra.Module.LinearMap.End

/-! # 完備加群を値に持つ線形写像の加群

列作用の一意解を各元で取り、解の一意性から線形性を証明する。
始域の有限生成性や射影性は不要である。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
variable (R : Type u) [CommRing R]

/-- 導来完備加群を値に持つ線形写像の加群も導来完備。 -/
theorem isModuleComplete_linearMap (f : R) (M N : ModuleCat.{u} R)
    (hN : IsModuleComplete R f N) :
    IsModuleComplete R f (ModuleCat.of R (M →ₗ[R] N)) := by
  have hn := (isModuleComplete_iff_recurrence_bijective R f N).mp hN
  apply (isModuleComplete_iff_recurrence_bijective R f _).mpr
  constructor
  · intro x y hxy
    have he (m : M) : (fun n ↦ x n m) = (fun n ↦ y n m) := hn.injective
      (congrArg (fun z n ↦ z n m) hxy)
    funext n
    apply LinearMap.ext
    intro m
    exact congrFun (he m) n
  · intro y
    choose x hx using fun m : M ↦ hn.surjective (fun n ↦ y n m)
    have hadd (a b : M) : x (a + b) = x a + x b := by
      apply hn.injective
      rw [map_add, hx, hx, hx]
      funext n
      exact (y n).map_add a b
    have hsmul (r : R) (a : M) : x (r • a) = r • x a := by
      apply hn.injective
      rw [map_smul, hx, hx]
      funext n
      exact (y n).map_smul r a
    let z : ℕ → M →ₗ[R] N := fun n ↦
      { toFun := fun a ↦ x a n
        map_add' := fun a b ↦ congrFun (hadd a b) n
        map_smul' := fun r a ↦ congrFun (hsmul r a) n }
    refine ⟨z, ?_⟩
    funext n
    apply LinearMap.ext
    intro m
    exact congrFun (hx m) n

end SerrePositivity.DerivedCompletion
