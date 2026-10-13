module

public import SerrePositivity.CLMST.Algebra
public import SerrePositivity.CommutativeAlgebra.RootTower.Stage
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.LocalRing.Basic

/-! # CLMST の有限段の基底変更

`D_n=A_n⊗_A D` を定め、D の右側の作用を標準化する。
零段の D との代数同型と、完備化した塔の perfectoid 化への標準写像を構成する。
このファイルは `Paper/` を import しない。
-/

@[expose] public noncomputable section
universe u
open scoped TensorProduct
open IsLocalRing

namespace SerrePositivity.CLMST
open Section2

variable (A D : Type u) [CommRing A] [CommRing D] [Algebra A D]
    {h : ℕ} (t : Fin h → A) (p : ℕ)

/-- CLMST の有限段の基底変更 `D_n=A_n⊗_A D`。
独立した型名により、D の右作用を通常のテンソル積の左作用と区別する。 -/
def StageAlgebra (n : ℕ) : Type u := TowerStage A t p n ⊗[A] D

instance stageAlgebraCommRing (n : ℕ) : CommRing (StageAlgebra A D t p n) :=
  inferInstanceAs (CommRing (TowerStage A t p n ⊗[A] D))

instance stageAlgebraBase (n : ℕ) : Algebra A (StageAlgebra A D t p n) :=
  inferInstanceAs (Algebra A (TowerStage A t p n ⊗[A] D))

instance stageAlgebraStage (n : ℕ) : Algebra (TowerStage A t p n) (StageAlgebra A D t p n) :=
  inferInstanceAs (Algebra (TowerStage A t p n) (TowerStage A t p n ⊗[A] D))

instance stageAlgebraD (n : ℕ) : Algebra D (StageAlgebra A D t p n) :=
  Algebra.TensorProduct.rightAlgebra

instance stageAlgebraScalarTowerStage (n : ℕ) :
    IsScalarTower A (TowerStage A t p n) (StageAlgebra A D t p n) :=
  inferInstanceAs (IsScalarTower A (TowerStage A t p n) (TowerStage A t p n ⊗[A] D))

instance stageAlgebraScalarTowerD (n : ℕ) : IsScalarTower A D (StageAlgebra A D t p n) := by
  let : Algebra D (TowerStage A t p n ⊗[A] D) := Algebra.TensorProduct.rightAlgebra
  exact inferInstanceAs (IsScalarTower A D (TowerStage A t p n ⊗[A] D))

/-- 零段では各根の関係が `X_i=t_i` となるので、基底環へ評価できる。 -/
def stage0ToBase : TowerStage A t p 0 →ₐ[A] A :=
  Ideal.Quotient.liftₐ (towerRel A t p 0) (MvPolynomial.aeval t) (by
    have hker : towerRel A t p 0 ≤ RingHom.ker (MvPolynomial.aeval t).toRingHom := by
      change Ideal.span (Set.range fun i : Fin h ↦
        MvPolynomial.X i ^ (p ^ 0) - MvPolynomial.C (t i)) ≤ _
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      simp [RingHom.mem_ker]
    intro f hf
    exact hker hf)

/-- 零段から基底環への写像は、多項式代表元を座標 t で評価する。 -/
@[simp] theorem stage0ToBase_mk (f : MvPolynomial (Fin h) A) :
    stage0ToBase A t p (Ideal.Quotient.mk (towerRel A t p 0) f) = MvPolynomial.aeval t f := rfl

/-- 根の塔の零段は、基底環 A と A 代数として同型。素数性や局所性は不要。 -/
def stage0BaseEquiv : TowerStage A t p 0 ≃ₐ[A] A := by
  refine AlgEquiv.ofAlgHom (stage0ToBase A t p) (Algebra.ofId A (TowerStage A t p 0)) ?_ ?_
  · ext
  · apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, AlgHom.id_apply, Ideal.Quotient.mkₐ_eq_mk,
      stage0ToBase_mk, MvPolynomial.aeval_X]
    change algebraMap A (TowerStage A t p 0) (t i) =
      Ideal.Quotient.mk (towerRel A t p 0) (MvPolynomial.X i)
    simpa only [pow_zero, pow_one] using (mk_X_pow A t p 0 i).symm

/-- `D_0=A_0⊗_A D` と D の、標準的な D 代数同型。 -/
def stage0Equiv : StageAlgebra A D t p 0 ≃ₐ[D] D := by
  letI : Algebra D (TowerStage A t p 0 ⊗[A] D) := Algebra.TensorProduct.rightAlgebra
  exact (Algebra.TensorProduct.commRight A D (TowerStage A t p 0)).symm.trans
    ((Algebra.TensorProduct.congr (AlgEquiv.refl : D ≃ₐ[D] D) (stage0BaseEquiv A t p)).trans
      (Algebra.TensorProduct.rid A D D))

/-- 零段同型は D の標準的な像を元へ戻す。 -/
@[simp] theorem stage0Equiv_algebraMap (d : D) :
    stage0Equiv A D t p (algebraMap D (StageAlgebra A D t p 0) d) = d :=
  (stage0Equiv A D t p).commutes d

/-- 零段への D の標準写像は単射。 -/
theorem stage0_algebraMap_injective :
    Function.Injective (algebraMap D (StageAlgebra A D t p 0)) := by
  intro x y hxy
  simpa using congrArg (stage0Equiv A D t p) hxy

/-- 零段への D の標準写像は全射。 -/
theorem stage0_algebraMap_surjective :
    Function.Surjective (algebraMap D (StageAlgebra A D t p 0)) := by
  intro x
  refine ⟨stage0Equiv A D t p x, ?_⟩
  apply (stage0Equiv A D t p).injective
  simp

instance stage0ModuleFinite : Module.Finite D (StageAlgebra A D t p 0) :=
  Module.Finite.of_surjective (Algebra.linearMap D (StageAlgebra A D t p 0))
    (stage0_algebraMap_surjective A D t p)

instance stage0IsLocalRing [IsLocalRing D] : IsLocalRing (StageAlgebra A D t p 0) := by
  have : Nontrivial (StageAlgebra A D t p 0) :=
    ⟨⟨(stage0Equiv A D t p).symm 0, (stage0Equiv A D t p).symm 1,
      fun h ↦ zero_ne_one ((stage0Equiv A D t p).symm.injective h)⟩⟩
  exact IsLocalRing.of_surjective' (algebraMap D (StageAlgebra A D t p 0))
    (stage0_algebraMap_surjective A D t p)

variable [IsNoetherianRing A] [Module.Finite A D] [Fact p.Prime]
    (hperf : IsIntegralPerfectoid (CompletedTower A t p) p)

/-- 有限段から塔・完備化を経由して `RPerfd` へ送る A 代数写像。 -/
def stageToRPerfd (n : ℕ) : TowerStage A t p n →ₐ[A] RPerfd A D t p hperf :=
  (IsScalarTower.toAlgHom A (CompletedTower A t p) (RPerfd A D t p hperf)).comp
    ((IsScalarTower.toAlgHom A (Tower A t p) (CompletedTower A t p)).comp
      (IsScalarTower.toAlgHom A (TowerStage A t p n) (Tower A t p)))

/-- 有限段の基底変更から `RPerfd` への標準 D 代数写像。 -/
def toRPerfd (n : ℕ) : StageAlgebra A D t p n →ₐ[D] RPerfd A D t p hperf := by
  letI : Algebra D (TowerStage A t p n ⊗[A] D) := Algebra.TensorProduct.rightAlgebra
  exact (Algebra.TensorProduct.lift (Algebra.ofId D (RPerfd A D t p hperf))
    (stageToRPerfd A D t p hperf n) (fun _ _ ↦ Commute.all _ _)).comp
      (Algebra.TensorProduct.commRight A D (TowerStage A t p n)).symm.toAlgHom

/-- 有限段を経由する D の作用は、既存の `RPerfd` 上の D の作用と一致する。 -/
@[simp] theorem toRPerfd_algebraMap_D (n : ℕ) (d : D) :
    toRPerfd A D t p hperf n (algebraMap D (StageAlgebra A D t p n) d) =
      algebraMap D (RPerfd A D t p hperf) d :=
  (toRPerfd A D t p hperf n).commutes d

end SerrePositivity.CLMST
