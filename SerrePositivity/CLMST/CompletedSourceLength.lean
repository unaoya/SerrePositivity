module

public import SerrePositivity.CLMST.CompletedStageBaseChange
public import SerrePositivity.CLMST.CompletedCokernelLength
public import SerrePositivity.CLMST.StageFiniteness
public import SerrePositivity.CLMST.StageLocality
public import SerrePositivity.HomologicalAlgebra.FlatKoszulFiniteness

/-! # 比較元の完備テンソル代数の Koszul 長さ

有限段のホモロジーを平坦な基底変更で完備塔へ移す。
完備塔上の有限生成性と台の条件から正規化長さの有限性を導く。
完備塔やテンソル代数の Noether 性、perfectoid 化の結果は用いない。
-/

@[expose] public noncomputable section
universe u
open scoped TensorProduct
namespace SerrePositivity.CLMST
open Section2 IsLocalRing CategoryTheory

variable (A D : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [CommRing D] [Algebra A D] [Module.Finite A D]
    {h : ℕ} (t : Fin h → A) (p : ℕ) [Fact p.Prime]
    (ht : ∀ i, t i ∈ maximalIdeal A)

omit [IsNoetherianRing A] in
/-- 有限段のパラメータ系にも、標準段写像を通じて台の条件を供給する。 -/
theorem completedTensorMaxIdeal_le_stage_parameter_radical
    (n : ℕ) [IsLocalRing (StageAlgebra A D t p n)]
    (hinj : Function.Injective (algebraMap A (StageAlgebra A D t p n)))
    {r : ℕ} (z : Fin r → StageAlgebra A D t p n)
    (hz : IsSystemOfParameters (StageAlgebra A D t p n) z) :
    completedTensorMaxIdeal A D t p ≤
      (Ideal.span (Set.range ((stageToCompletedTensor A D t p n).toRingHom ∘ z))).radical := by
  let φ := (stageToCompletedTensor A D t p n).toRingHom
  have hc : φ.comp (algebraMap A (StageAlgebra A D t p n)) =
      algebraMap A ((CompletedTower A t p) ⊗[A] D) := by
    ext a
    exact (stageToCompletedTensor A D t p n).commutes a
  have hm := Ideal.map_mono (f := φ)
    (maximalIdeal_map_le_of_finite_of_injective A (StageAlgebra A D t p n) hinj)
  rw [Ideal.map_map, hc] at hm
  apply hm.trans
  rw [← hz.2]
  have hr : (Ideal.span (Set.range z)).radical.map φ ≤
      ((Ideal.span (Set.range z)).map φ).radical := Ideal.map_radical_le φ
  convert hr using 1
  rw [Ideal.map_span, ← Set.range_comp]

omit [IsLocalRing A] in
/-- 底環からの直接の基底変更でも、比較元の全次数の Koszul ホモロジーは完備塔上有限生成。 -/
theorem completedTensor_koszulModuleHomology_finite
    {r : ℕ} (z : Fin r → D) (q : ℤ) :
    let S := (CompletedTower A t p) ⊗[A] D
    let M := (((koszulModuleFunctor
      (Algebra.TensorProduct.includeRight.toRingHom ∘ z)).obj (ModuleCat.of S S)).homology q)
    let _ := Module.compHom M (algebraMap (CompletedTower A t p) S)
    Module.Finite (CompletedTower A t p) M := by
  let : IsNoetherianRing D := IsNoetherianRing.of_finite A D
  let := flat_completedTower_over_base A t p
  let : Algebra D ((CompletedTower A t p) ⊗[A] D) := Algebra.TensorProduct.rightAlgebra
  exact pushout_koszulModuleHomology_finite A (CompletedTower A t p) D
    ((CompletedTower A t p) ⊗[A] D) z q

/-- 台の条件を満たす列について、比較元の全次数の正規化 Koszul 長さは有限。 -/
theorem completedTensor_koszul_length_ne_top
    (hp : (p : A) ∈ maximalIdeal A) {r : ℕ} (z : Fin r → D)
    (hJ : completedTensorMaxIdeal A D t p ≤
      (Ideal.span (Set.range (Algebra.TensorProduct.includeRight.toRingHom ∘ z))).radical)
    (q : ℤ) :
    (completedTensorLength A D t p ht).len
      (((koszulModuleFunctor (Algebra.TensorProduct.includeRight.toRingHom ∘ z)).obj
        (ModuleCat.of ((CompletedTower A t p) ⊗[A] D)
          ((CompletedTower A t p) ⊗[A] D))).homology q) ≠ ⊤ := by
  exact completedTensorLength_ne_top_of_finite A D t p ht hp _
    (completedTensor_koszulModuleHomology_finite A D t p z q)
    (isPowTorsion_koszulModuleHomology (completedTensorMaxIdeal_fg A D t p)
      (Algebra.TensorProduct.includeRight.toRingHom ∘ z) hJ
      (ModuleCat.of ((CompletedTower A t p) ⊗[A] D) ((CompletedTower A t p) ⊗[A] D)) q)

omit [IsLocalRing A] in
/-- 任意の有限段から来る列でも、比較元のホモロジーは完備塔上有限生成。 -/
theorem completedTensor_stage_koszulModuleHomology_finite
    (n : ℕ) {r : ℕ} (z : Fin r → StageAlgebra A D t p n) (q : ℤ) :
    let S := (CompletedTower A t p) ⊗[A] D
    let M := (((koszulModuleFunctor
      ((stageToCompletedTensor A D t p n).toRingHom ∘ z)).obj (ModuleCat.of S S)).homology q)
    let _ := Module.compHom M (algebraMap (CompletedTower A t p) S)
    Module.Finite (CompletedTower A t p) M := by
  let := completedTensorStageAlgebra A D t p n
  let := completedTensorStageScalarTower A D t p n
  let := completedTensorStageIsPushout A D t p n
  let := flat_completedTower_over_stage A t p n
  let : Module.Finite (TowerStage A t p n) (StageAlgebra A D t p n) :=
    Module.Finite.of_restrictScalars_finite A _ _
  exact pushout_koszulModuleHomology_finite (TowerStage A t p n)
    (CompletedTower A t p) (StageAlgebra A D t p n)
    ((CompletedTower A t p) ⊗[A] D) z q

/-- 有限段の列の台の条件から、完備テンソル代数の全 Koszul 長さの有限性を導く。 -/
theorem completedTensor_stage_koszul_length_ne_top
    (hp : (p : A) ∈ maximalIdeal A) (n : ℕ) {r : ℕ}
    (z : Fin r → StageAlgebra A D t p n)
    (hJ : completedTensorMaxIdeal A D t p ≤
      (Ideal.span (Set.range ((stageToCompletedTensor A D t p n).toRingHom ∘ z))).radical)
    (q : ℤ) :
    (completedTensorLength A D t p ht).len
      (((koszulModuleFunctor ((stageToCompletedTensor A D t p n).toRingHom ∘ z)).obj
        (ModuleCat.of ((CompletedTower A t p) ⊗[A] D)
          ((CompletedTower A t p) ⊗[A] D))).homology q) ≠ ⊤ := by
  exact completedTensorLength_ne_top_of_finite A D t p ht hp _
    (completedTensor_stage_koszulModuleHomology_finite A D t p n z q)
    (isPowTorsion_koszulModuleHomology (completedTensorMaxIdeal_fg A D t p)
      ((stageToCompletedTensor A D t p n).toRingHom ∘ z) hJ
      (ModuleCat.of ((CompletedTower A t p) ⊗[A] D) ((CompletedTower A t p) ⊗[A] D)) q)

/-- 有限段のパラメータ系では台の条件も自動的に満たす。 -/
theorem completedTensor_stage_parameter_source_length_ne_top
    (hp : (p : A) ∈ maximalIdeal A) (n : ℕ) [IsLocalRing (StageAlgebra A D t p n)]
    (hinj : Function.Injective (algebraMap A (StageAlgebra A D t p n)))
    {r : ℕ} (z : Fin r → StageAlgebra A D t p n)
    (hz : IsSystemOfParameters (StageAlgebra A D t p n) z) (q : ℤ) :
    (completedTensorLength A D t p ht).len
      (((koszulModuleFunctor ((stageToCompletedTensor A D t p n).toRingHom ∘ z)).obj
        (ModuleCat.of ((CompletedTower A t p) ⊗[A] D)
          ((CompletedTower A t p) ⊗[A] D))).homology q) ≠ ⊤ :=
  completedTensor_stage_koszul_length_ne_top A D t p ht hp n z
    (completedTensorMaxIdeal_le_stage_parameter_radical A D t p n hinj z hz) q

/-- D のパラメータ系では、台と有限生成性をともに構成から供給できる。 -/
theorem completedTensor_parameter_source_length_ne_top
    [IsLocalRing D] (hp : (p : A) ∈ maximalIdeal A)
    (hinj : Function.Injective (algebraMap A D))
    (z : Fin h → D) (hz : IsSystemOfParameters D z) (q : ℤ) :
    (completedTensorLength A D t p ht).len
      (((koszulModuleFunctor (Algebra.TensorProduct.includeRight.toRingHom ∘ z)).obj
        (ModuleCat.of ((CompletedTower A t p) ⊗[A] D)
          ((CompletedTower A t p) ⊗[A] D))).homology q) ≠ ⊤ :=
  completedTensor_koszul_length_ne_top A D t p ht hp z
    (completedTensorMaxIdeal_le_parameter_radical A D t p hinj z hz) q

end SerrePositivity.CLMST
