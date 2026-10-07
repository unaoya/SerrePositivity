module

public import SerrePositivity.Koszul
public import SerrePositivity.Perfect
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Koszul 複体の基底変更

環準同型 `φ : A → C` による係数拡大（`baseChange φ`）は Koszul 複体と両立する：
`C ⊗_A K(z; A) ≅ K(φ z; C)`。写像錐の反復で定義したので、
写像錐が加法的関手と両立すること（`homotopyCofiber.mapHomologicalComplexObjIso`）と、
係数拡大が `a • 𝟙` を `φ a • 𝟙` に送ることから、`n` の帰納法で出る。
-/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped ChangeOfRings

namespace SerrePositivity

variable {A C : Type u} [CommRing A] [CommRing C] (φ : A →+* C)

/-- 係数拡大は射のスカラー倍を `φ` 倍に送る。 -/
lemma extendScalars_map_smul {M N : ModuleCat.{u} A} (f : M ⟶ N) (a : A) :
    (ModuleCat.extendScalars.{u, u, u} φ).map (a • f) =
      φ a • (ModuleCat.extendScalars.{u, u, u} φ).map f := by
  ext m
  change ((1 : C) ⊗ₜ[A, φ] (a • f m) : (ModuleCat.extendScalars φ).obj N) =
    (φ a * 1) ⊗ₜ[A, φ] f m
  let _ : Module A C := Module.compHom C φ
  change (1 : C) ⊗ₜ[A] (a • f m) = (φ a * 1) ⊗ₜ[A] f m
  rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  rfl

/-- 係数拡大は `a • 𝟙 K` を `φ a • 𝟙` に送る。 -/
lemma baseChange_smulId (K : CochainComplex (ModuleCat.{u} A) ℤ) (a : A) :
    ((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex _).map (smulId a K) =
      smulId (φ a) (baseChange φ K) := by
  ext i
  simp [smulId, extendScalars_map_smul]

/-- 基底変更と Koszul 複体の両立：`C ⊗_A K(z; A) ≅ K(φ z; C)`。 -/
noncomputable def baseChangeKoszulIso :
    ∀ {n : ℕ} (z : Fin n → A), baseChange φ (koszulComplex z) ≅ koszulComplex (φ ∘ z)
  | 0, z =>
    (HomologicalComplex.singleMapHomologicalComplex (ModuleCat.extendScalars.{u, u, u} φ)
      (c := ComplexShape.up ℤ) 0).app (ModuleCat.of A A) ≪≫
    (HomologicalComplex.single (ModuleCat.{u} C) (ComplexShape.up ℤ) 0).mapIso
      (letI := φ.toAlgebra; (TensorProduct.AlgebraTensorModule.rid A C C).toModuleIso)
  | n + 1, z => by
    change baseChange φ (CochainComplex.mappingCone
      (smulId (z (Fin.last n)) (koszulComplex (Fin.init z)))) ≅
      CochainComplex.mappingCone (smulId (φ (z (Fin.last n))) (koszulComplex (Fin.init (φ ∘ z))))
    refine HomologicalComplex.homotopyCofiber.mapHomologicalComplexObjIso _ _ ≪≫ ?_
    rw [baseChange_smulId]
    exact HomologicalComplex.homotopyCofiber.mapArrowIso _ _ (fun j ↦ ⟨j - 1, by simp⟩)
      (Arrow.isoMk (baseChangeKoszulIso (Fin.init z)) (baseChangeKoszulIso (Fin.init z))
        (by simp [smulId]))

end SerrePositivity
