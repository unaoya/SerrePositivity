module

public import SerrePositivity.HomologicalAlgebra.Basic
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.Basis.Prod
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Finiteness.Prod
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# 複体の項の自由性・有限性

零加群・biproduct・写像錐の項が有限自由であること。
Noether 環上では、各項が有限生成な複体のホモロジーも有限生成（`homology_moduleFinite`）。
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace SerrePositivity

variable {R : Type u} [CommRing R]

lemma isZero_moduleCat_free {M : ModuleCat.{u} R} (h : IsZero M) : Module.Free R M := by
  have : Subsingleton M := ModuleCat.isZero_iff_subsingleton.mp h
  infer_instance

lemma isZero_moduleCat_finite {M : ModuleCat.{u} R} (h : IsZero M) : Module.Finite R M := by
  have : Subsingleton M := ModuleCat.isZero_iff_subsingleton.mp h
  infer_instance

/-- 二つの加群の biproduct は自由・有限を保つ。 -/
lemma free_finite_biprod (M N : ModuleCat.{u} R) [Module.Free R M] [Module.Free R N]
    [Module.Finite R M] [Module.Finite R N] :
    Module.Free R (M ⊞ N : ModuleCat.{u} R) ∧ Module.Finite R (M ⊞ N : ModuleCat.{u} R) := by
  let e : (M ⊞ N : ModuleCat.{u} R) ≃ₗ[R] (M × N) := (ModuleCat.biprodIsoProd M N).toLinearEquiv
  exact ⟨Module.Free.of_equiv e.symm, Module.Finite.equiv e.symm⟩

/-- 写像錐の項は自由・有限を保つ。 -/
lemma mappingCone_free_finite {X Y : CochainComplex (ModuleCat.{u} R) ℤ} (f : X ⟶ Y) (i : ℤ)
    [Module.Free R (X.X (i + 1))] [Module.Free R (Y.X i)]
    [Module.Finite R (X.X (i + 1))] [Module.Finite R (Y.X i)] :
    Module.Free R ((CochainComplex.mappingCone f).X i) ∧
      Module.Finite R ((CochainComplex.mappingCone f).X i) := by
  let e := (HomologicalComplex.homotopyCofiber.XIsoBiprod f i (i + 1) rfl).toLinearEquiv
  obtain ⟨h1, h2⟩ := free_finite_biprod (X.X (i + 1)) (Y.X i)
  exact ⟨Module.Free.of_equiv e.symm, Module.Finite.equiv e.symm⟩

/-- Noether 環上、各項が有限生成な複体のホモロジーは有限生成。 -/
lemma homology_moduleFinite [IsNoetherianRing R] (P : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ)
    [Module.Finite R (P.X i)] : Module.Finite R (P.homology i) := by
  let S := P.sc i
  have : Module.Finite R S.X₂ := inferInstanceAs (Module.Finite R (P.X i))
  have : Module.Finite R S.moduleCatLeftHomologyData.H := by
    change Module.Finite R (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles)
    infer_instance
  exact Module.Finite.equiv S.moduleCatHomologyIso.toLinearEquiv.symm

end SerrePositivity
