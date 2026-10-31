module

public import SerrePositivity.CLMST.CompletedSourceLength
public import SerrePositivity.CLMST.StageResidueLength
public import SerrePositivity.LengthAlgebra.RootTowerLength.Completion
public import SerrePositivity.CommutativeAlgebra.KoszulMultiplicity.Formula
public import SerrePositivity.CommutativeAlgebra.Koszul.FiniteLength

/-! # 比較元の Euler 評価の有限段での計算

平坦な基底変更の実際のホモロジー同型で有限段へ戻し、完備化前後の長さ比較と
共通剰余体による通常長さの一致を用いる。完備塔の Noether 性や
perfectoid 化の引用は使用しない。
-/

@[expose] public noncomputable section
universe u
open scoped TensorProduct ENNReal
namespace SerrePositivity.CLMST
open Section2 IsLocalRing CategoryTheory
set_option backward.isDefEq.respectTransparency false

variable (A D : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [CommRing D] [IsLocalRing D] [IsNoetherianRing D] [Algebra A D]
    {h : ℕ} (t : Fin h → A) (p : ℕ) [Fact p.Prime]
    (ht : ∀ i, t i ∈ maximalIdeal A)
    (hp : (p : A) ∈ maximalIdeal A)
    (htD : ∀ i, algebraMap A D (t i) ∈ maximalIdeal D)
    (hres : Function.Surjective ((residue D).comp (algebraMap A D)))

include ht hp htD hres in
/-- 各次数の比較元の正規化長さは、有限段の通常長さを段の階数で割った値。 -/
theorem completedTensor_stage_source_homology_length
    (n : ℕ) {r : ℕ} (y : Fin r → StageAlgebra A D t p n)
    (hy : let _ := stageAlgebra_isLocalRing A D t p htD n
      IsSystemOfParameters (StageAlgebra A D t p n) y) (q : ℤ) :
    (completedTensorLength A D t p ht).len
      (((koszulModuleFunctor ((stageToCompletedTensor A D t p n).toRingHom ∘ y)).obj
        (ModuleCat.of ((CompletedTower A t p) ⊗[A] D)
          ((CompletedTower A t p) ⊗[A] D))).homology q) =
    (Module.length (StageAlgebra A D t p n) ((koszulComplex y).homology q) : ℝ≥0∞) /
      (stageRank h p n : ℝ≥0∞) := by
  let := stageAlgebra_isLocalRing A D t p htD n
  let := completedTensorStageAlgebra A D t p n
  let := completedTensorStageScalarTower A D t p n
  let := completedTensorStageIsPushout A D t p n
  let := flat_completedTower_over_stage A t p n
  rw [koszulModuleFunctor_self_eq]
  let H := (koszulComplex y).homology q
  let N := (koszulComplex ((stageToCompletedTensor A D t p n).toRingHom ∘ y)).homology q
  let : Module (TowerStage A t p n) H := Module.compHom H
    (algebraMap (TowerStage A t p n) (StageAlgebra A D t p n))
  let : Module (CompletedTower A t p) N := Module.compHom N
    (algebraMap (CompletedTower A t p) ((CompletedTower A t p) ⊗[A] D))
  have hlength : Module.length (TowerStage A t p n) H =
      Module.length (StageAlgebra A D t p n) H :=
    length_restrictScalars_stageAlgebra_eq A D t p htD hres n H
  have hfinite : IsFiniteLength (TowerStage A t p n) H := by
    apply Module.length_ne_top_iff.mp
    rw [hlength]
    exact Module.length_ne_top_iff.mpr
      (isFiniteLength_koszulHomology_of_isSystemOfParameters _ y hy q)
  let e : N ≃ₗ[CompletedTower A t p]
      (CompletedTower A t p ⊗[TowerStage A t p n] H) :=
    pushoutKoszulHomologyEquiv (TowerStage A t p n) (CompletedTower A t p)
    (StageAlgebra A D t p n) ((CompletedTower A t p) ⊗[A] D) y q
  change (RootTowerLength.completedNormalizedLength A t p ht).len N = _
  rw [(RootTowerLength.completedNormalizedLength A t p ht).len_congr _ _ e]
  rw [RootTowerLength.completedNormalizedLength_tensor_eq_length A t p ht hp n H hfinite]
  rw [hlength]

include ht hp htD hres in
/-- 比較元の Euler 評価は有限段の通常の Koszul Euler 数を正規化した値。 -/
theorem completedTensor_stage_source_euler_eq_chiOrd
    (n : ℕ) {r : ℕ} (y : Fin r → StageAlgebra A D t p n)
    (hy : let _ := stageAlgebra_isLocalRing A D t p htD n
      IsSystemOfParameters (StageAlgebra A D t p n) y) :
    lambdaEuler (completedTensorLength A D t p ht)
      ((koszulModuleFunctor ((stageToCompletedTensor A D t p n).toRingHom ∘ y)).obj
        (ModuleCat.of ((CompletedTower A t p) ⊗[A] D) ((CompletedTower A t p) ⊗[A] D))) =
      chiOrd (koszulComplex y) / (stageRank h p n : ℝ) := by
  unfold lambdaEuler chiOrd
  simp only [completedTensor_stage_source_homology_length A D t p ht hp htD hres n y hy,
    ENNReal.toReal_div, ENNReal.toReal_natCast, toReal_toENNReal]
  simp only [div_eq_mul_inv, ← mul_assoc, finsum_mul]

include ht hp htD hres in
/-- 証明済みの Koszul 重複度公式により、比較元の Euler 評価は有限段の重複度の正規化。 -/
theorem completedTensor_stage_source_euler_eq_multiplicity
    (n : ℕ) {r : ℕ} (y : Fin r → StageAlgebra A D t p n)
    (hy : let _ := stageAlgebra_isLocalRing A D t p htD n
      IsSystemOfParameters (StageAlgebra A D t p n) y) :
    lambdaEuler (completedTensorLength A D t p ht)
      ((koszulModuleFunctor ((stageToCompletedTensor A D t p n).toRingHom ∘ y)).obj
        (ModuleCat.of ((CompletedTower A t p) ⊗[A] D) ((CompletedTower A t p) ⊗[A] D))) =
      (HilbertSamuel.multiplicity (StageAlgebra A D t p n)
        (Ideal.span (Set.range y)) (StageAlgebra A D t p n) : ℝ) / (stageRank h p n : ℝ) := by
  let := stageAlgebra_isLocalRing A D t p htD n
  rw [completedTensor_stage_source_euler_eq_chiOrd A D t p ht hp htD hres n y hy,
    KoszulMultiplicity.multiplicity_eq_chiOrd_koszul y hy]

end SerrePositivity.CLMST
