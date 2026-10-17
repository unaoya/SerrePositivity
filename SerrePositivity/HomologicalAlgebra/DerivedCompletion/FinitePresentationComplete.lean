module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleClosure
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ReflectionTransport
public import Mathlib.Algebra.Module.FinitePresentation

/-! # 有限表示加群の導来完備性

有限表示を有限自由加群間の写像の余核として用いる。
Noether 性、古典的完備性、torsion の有界性は要求しない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.DerivedCompletion
variable (R : Type u) [CommRing R] (a : R)

/-- 導来完備な環上の有限表示加群は導来完備。 -/
theorem isModuleComplete_of_finitePresentation
    (hR : IsModuleComplete R a (ModuleCat.of R R))
    (M : ModuleCat.{u} R) [Module.FinitePresentation R M] :
    IsModuleComplete R a M := by
  obtain ⟨n, K, e, hK⟩ := Module.FinitePresentation.exists_fin R M
  obtain ⟨m, g, hg⟩ := K.fg_iff_exists_fin_linearMap.mp hK
  have hc := isModuleComplete_coker R a g
    (isModuleComplete_pi R a (fun _ : Fin m => ModuleCat.of R R) (fun _ => hR))
    (isModuleComplete_pi R a (fun _ : Fin n => ModuleCat.of R R) (fun _ => hR))
  rw [hg] at hc
  exact isModuleComplete_of_linearEquiv R a _ M e.symm hc

end SerrePositivity.DerivedCompletion
