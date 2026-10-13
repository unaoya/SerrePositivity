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

variable [IsNoetherianRing A] [Module.Finite A D] [Fact p.Prime]
    (hperf : IsIntegralPerfectoid (CompletedTower A t p) p)

/-- 完備テンソル代数を経由する標準写像は、既存の有限段からの普遍写像と一致する。 -/
theorem stageToCompletedTensor_toMixedPerfectoid (n : ℕ) (x : StageAlgebra A D t p n) :
    toMixedPerfectoid A D t p hperf (stageToCompletedTensor A D t p n x) =
      toRPerfd A D t p hperf n x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy =>
    calc
      _ = toMixedPerfectoid A D t p hperf (stageToCompletedTensor A D t p n x) +
          toMixedPerfectoid A D t p hperf (stageToCompletedTensor A D t p n y) :=
        (congrArg (toMixedPerfectoid A D t p hperf)
          ((stageToCompletedTensor A D t p n).map_add x y)).trans
            ((toMixedPerfectoid A D t p hperf).map_add _ _)
      _ = toRPerfd A D t p hperf n x + toRPerfd A D t p hperf n y :=
        congrArg₂ (· + ·) hx hy
      _ = _ := ((toRPerfd A D t p hperf n).map_add x y).symm
  | tmul a d =>
    let : Algebra D (TowerStage A t p n ⊗[A] D) := Algebra.TensorProduct.rightAlgebra
    have hrhs : toRPerfd A D t p hperf n (a ⊗ₜ[A] d) =
        algebraMap D (RPerfd A D t p hperf) d * stageToRPerfd A D t p hperf n a := by
      change (Algebra.TensorProduct.lift (Algebra.ofId D (RPerfd A D t p hperf))
        (stageToRPerfd A D t p hperf n) (fun _ _ ↦ Commute.all _ _))
        ((Algebra.TensorProduct.commRight A D (TowerStage A t p n)).symm (a ⊗ₜ[A] d)) = _
      rw [Algebra.TensorProduct.commRight_symm_tmul, Algebra.TensorProduct.lift_tmul]
      rfl
    rw [hrhs, stageToCompletedTensor_tmul]
    calc
      _ = toMixedPerfectoid A D t p hperf (stageToCompletedTower A t p n a ⊗ₜ[A] (1 : D)) *
          toMixedPerfectoid A D t p hperf ((1 : CompletedTower A t p) ⊗ₜ[A] d) := by
        rw [← map_mul]
        congr 1
        simp
      _ = stageToRPerfd A D t p hperf n a * algebraMap D (RPerfd A D t p hperf) d := rfl
      _ = _ := mul_comm _ _

/-- 段写像の合成の一致を環準同型の等式として公開する。 -/
theorem toRPerfd_eq_toMixedPerfectoid_comp_stage (n : ℕ) :
    (toRPerfd A D t p hperf n).toRingHom =
      (toMixedPerfectoid A D t p hperf).comp (stageToCompletedTensor A D t p n).toRingHom := by
  apply RingHom.ext
  intro x
  exact (stageToCompletedTensor_toMixedPerfectoid A D t p hperf n x).symm

end SerrePositivity.CLMST
