module
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Freeness and finite generation under extension of scalars -/
@[expose] public section
universe u
namespace SerrePositivity
variable {A C : Type u} [CommRing A] [CommRing C]

/-- `A` 加群 `M` が自由なら、係数拡大 `C ⊗_A M` は `C` 加群として自由（Mathlib のテンソル積の
インスタンス）。 -/
lemma free_baseChange (φ : A →+* C) (M : ModuleCat.{u} A) [Module.Free A M] :
    Module.Free C ((ModuleCat.extendScalars.{u, u, u} φ).obj M) := by
  let := φ.toAlgebra
  change Module.Free C (TensorProduct A C M)
  infer_instance

/-- `A` 加群 `M` が有限生成なら、係数拡大 `C ⊗_A M` は `C` 加群として有限生成。 -/
lemma finite_baseChange (φ : A →+* C) (M : ModuleCat.{u} A) [Module.Finite A M] :
    Module.Finite C ((ModuleCat.extendScalars.{u, u, u} φ).obj M) := by
  let := φ.toAlgebra
  change Module.Finite C (TensorProduct A C M)
  infer_instance

end SerrePositivity
