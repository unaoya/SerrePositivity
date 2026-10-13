module

public import SerrePositivity.CLMST.StageParameterChange
public import SerrePositivity.CLMST.StageTensor

/-! # 最後のパラメータの冪の所属を完備テンソル代数へ移す

D の非単元正則元の正の冪に、有限段のパラメータ変更を適用する。
最後の元の適切な冪が、先頭の列と零化スカラーで生成されるイデアルに属することを、
実際の有限段から完備テンソル代数への写像で輸送する。
基底環の元 g を用いる場合には、輸送されたスカラーが g の標準像の冪と一致する。
-/

@[expose] public noncomputable section
universe u
open scoped TensorProduct
namespace SerrePositivity.CLMST
open Section2 IsLocalRing

variable (A D : Type u) [CommRing A] [CommRing D] [Algebra A D]
    {h : ℕ} (t : Fin h → A) (p : ℕ)

/-- 有限段における D の係数の標準像は、完備テンソル代数の右因子の標準像へ送られる。 -/
@[simp] theorem stageToCompletedTensor_algebraMap_D (n : ℕ) (a : D) :
    stageToCompletedTensor A D t p n (algebraMap D (StageAlgebra A D t p n) a) =
      (1 : CompletedTower A t p) ⊗ₜ[A] a := by
  change stageToCompletedTensor A D t p n ((1 : TowerStage A t p n) ⊗ₜ[A] a) = _
  rw [stageToCompletedTensor_tmul, map_one]

/-- 基底環の係数を D と有限段を経由して移しても、完備テンソル代数の標準係数に一致する。 -/
@[simp] theorem stageToCompletedTensor_algebraMap_D_base (n : ℕ) (g : A) :
    stageToCompletedTensor A D t p n
      (algebraMap D (StageAlgebra A D t p n) (algebraMap A D g)) =
      algebraMap A ((CompletedTower A t p) ⊗[A] D) g := by
  rw [← IsScalarTower.algebraMap_apply A D (StageAlgebra A D t p n),
    stageToCompletedTensor_algebraMap]

variable [IsNoetherianRing A] [IsLocalRing D] [Module.Finite A D] [Fact p.Prime]

/-- 正の零化指数 N に合わせて有限段の列を変更し、最後の元の正の冪の所属を
完備テンソル代数へ輸送する。元の生成イデアルを保ち、変更後の冪付き列もパラメータ系。 -/
theorem stage_parameter_power_selection_completed_of_regular_D
    (htD : ∀ i, algebraMap A D (t i) ∈ maximalIdeal D)
    (n : ℕ) (a : D) (haM : a ∈ maximalIdeal D) (ha : IsSMulRegular D a)
    (N : ℕ) (hN : 0 < N) :
    let _ := stageAlgebra_isLocalRing A D t p htD n
    ∀ {r : ℕ} (y : Fin (r + 1) → StageAlgebra A D t p n),
      IsSystemOfParameters (StageAlgebra A D t p n) y →
      ∃ (y' : Fin (r + 1) → StageAlgebra A D t p n) (k : ℕ),
        Ideal.span (Set.range y') = Ideal.span (Set.range y) ∧ 0 < k ∧
        IsSystemOfParameters (StageAlgebra A D t p n)
          (Fin.snoc (Fin.init y') (y' (Fin.last r) ^ k)) ∧
        stageToCompletedTensor A D t p n
          ((Fin.snoc (Fin.init y') (y' (Fin.last r) ^ k)) (Fin.last r)) ∈
            Ideal.span (Set.range (stageToCompletedTensor A D t p n ∘ Fin.init y')) ⊔
              Ideal.span {(stageToCompletedTensor A D t p n
                (algebraMap D (StageAlgebra A D t p n) a)) ^ N} := by
  let := stageAlgebra_isLocalRing A D t p htD n
  dsimp only
  intro r y hy
  obtain ⟨y', k, hspan, hk, hparams, hmem⟩ :=
    stage_parameter_power_selection_of_regular_D A D t p htD n (a ^ N)
      (Ideal.pow_mem_of_mem _ haM N hN) (ha.pow N) y hy
  refine ⟨y', k, hspan, hk, hparams, ?_⟩
  have hmapped := Ideal.mem_map_of_mem (stageToCompletedTensor A D t p n).toRingHom hmem
  simpa only [Fin.snoc_last, Ideal.map_sup, Ideal.map_span, Set.image_singleton,
    ← Set.range_comp, map_pow, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using hmapped

/-- 基底環の元 g の D 内の像が非単元正則なら、変更後の最後の元の冪は、
完備テンソル代数で先頭列の像と g^N の標準像が生成するイデアルに属する。 -/
theorem stage_parameter_power_selection_completed_of_regular_base
    (htD : ∀ i, algebraMap A D (t i) ∈ maximalIdeal D)
    (n : ℕ) (g : A) (hgM : algebraMap A D g ∈ maximalIdeal D)
    (hg : IsSMulRegular D (algebraMap A D g)) (N : ℕ) (hN : 0 < N) :
    let _ := stageAlgebra_isLocalRing A D t p htD n
    ∀ {r : ℕ} (y : Fin (r + 1) → StageAlgebra A D t p n),
      IsSystemOfParameters (StageAlgebra A D t p n) y →
      ∃ (y' : Fin (r + 1) → StageAlgebra A D t p n) (k : ℕ),
        Ideal.span (Set.range y') = Ideal.span (Set.range y) ∧ 0 < k ∧
        IsSystemOfParameters (StageAlgebra A D t p n)
          (Fin.snoc (Fin.init y') (y' (Fin.last r) ^ k)) ∧
        stageToCompletedTensor A D t p n
          ((Fin.snoc (Fin.init y') (y' (Fin.last r) ^ k)) (Fin.last r)) ∈
            Ideal.span (Set.range (stageToCompletedTensor A D t p n ∘ Fin.init y')) ⊔
              Ideal.span {(algebraMap A ((CompletedTower A t p) ⊗[A] D) g) ^ N} := by
  let := stageAlgebra_isLocalRing A D t p htD n
  dsimp only
  intro r y hy
  simpa only [stageToCompletedTensor_algebraMap_D_base] using
    stage_parameter_power_selection_completed_of_regular_D A D t p htD n
      (algebraMap A D g) hgM hg N hN y hy

end SerrePositivity.CLMST
