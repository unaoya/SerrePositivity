module

public import SerrePositivity.CommutativeAlgebra.Koszul
public import SerrePositivity.HomologicalAlgebra.BaseChange
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
