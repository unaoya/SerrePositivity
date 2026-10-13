module

public import SerrePositivity.CLMST.StageAlgebra

/-! # 有限段の基底変更から完備塔上のテンソル代数への写像

perfectoid 化を経由する前の標準写像を明示し、余核の係数制限にも使う。
-/

@[expose] public noncomputable section
universe u
open scoped TensorProduct
namespace SerrePositivity.CLMST
open Section2
variable (A D : Type u) [CommRing A] [CommRing D] [Algebra A D]
    {h : ℕ} (t : Fin h → A) (p : ℕ)

/-- 有限段から未完備塔・完備塔への標準 A 代数写像。 -/
def stageToCompletedTower (n : ℕ) : TowerStage A t p n →ₐ[A] CompletedTower A t p :=
  (IsScalarTower.toAlgHom A (Tower A t p) (CompletedTower A t p)).comp
    (IsScalarTower.toAlgHom A (TowerStage A t p n) (Tower A t p))

/-- D_n=A_n⊗_A D から A∞⊗_A D への標準 A 代数写像。 -/
def stageToCompletedTensor (n : ℕ) : StageAlgebra A D t p n →ₐ[A]
    (CompletedTower A t p) ⊗[A] D :=
  Algebra.TensorProduct.map (stageToCompletedTower A t p n) (AlgHom.id A D)

@[simp] theorem stageToCompletedTensor_algebraMap (n : ℕ) (a : A) :
    stageToCompletedTensor A D t p n (algebraMap A (StageAlgebra A D t p n) a) =
      algebraMap A ((CompletedTower A t p) ⊗[A] D) a :=
  (stageToCompletedTensor A D t p n).commutes a

@[simp] theorem stageToCompletedTensor_tmul (n : ℕ) (a : TowerStage A t p n) (d : D) :
    stageToCompletedTensor A D t p n (a ⊗ₜ[A] d) =
      stageToCompletedTower A t p n a ⊗ₜ[A] d := by
  change Algebra.TensorProduct.map (stageToCompletedTower A t p n) (AlgHom.id A D)
    (a ⊗ₜ[A] d) = _
  rw [Algebra.TensorProduct.map_tmul]
  rfl

end SerrePositivity.CLMST
