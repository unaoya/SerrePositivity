module

public import SerrePositivity.CLMST.StageLocality
public import SerrePositivity.CommutativeAlgebra.SystemOfParameters.Generators
public import SerrePositivity.CommutativeAlgebra.RootTower.Completion
public import Mathlib.RingTheory.Flat.Basic

/-! # 有限段への生成イデアルを保つパラメータ変更の適用

有限段の自由性で正則性を移し、局所性・極大イデアル所属を実構成から確認する。
有限段そのものが整域であるという仮定は置かない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.CLMST
open Section2 IsLocalRing
variable (A D : Type u) [CommRing A] [IsNoetherianRing A]
    [CommRing D] [IsLocalRing D] [Algebra A D] [Module.Finite A D]
    {h : ℕ} (t : Fin h → A) (p : ℕ) [Fact p.Prime]

omit [IsNoetherianRing A] [IsLocalRing D] [Module.Finite A D] in
/-- Dで正則な元は、D上自由な有限段でも正則。 -/
theorem isSMulRegular_stageAlgebra_of_regular_D (n : ℕ) (a : D)
    (ha : IsSMulRegular D a) : IsSMulRegular (StageAlgebra A D t p n)
      (algebraMap D (StageAlgebra A D t p n) a) := by
  let := stageAlgebra_free A D t p n
  exact ha.of_flat

/-- 有限段の任意のパラメータ系を、Dの非単元正則元に合わせて同じ生成イデアルのまま変更。 -/
theorem stage_parameter_change_of_regular_D
    (htD : ∀ i, algebraMap A D (t i) ∈ maximalIdeal D)
    (n : ℕ) (a : D) (haM : a ∈ maximalIdeal D) (ha : IsSMulRegular D a) :
    let _ := stageAlgebra_isLocalRing A D t p htD n
    ∀ {r : ℕ} (y : Fin (r + 1) → StageAlgebra A D t p n),
      IsSystemOfParameters (StageAlgebra A D t p n) y →
      ∃ y' : Fin (r + 1) → StageAlgebra A D t p n,
        Ideal.span (Set.range y') = Ideal.span (Set.range y) ∧
        IsSystemOfParameters (StageAlgebra A D t p n)
          (Fin.snoc (Fin.init y') (algebraMap D (StageAlgebra A D t p n) a)) := by
  let := stageAlgebra_isLocalRing A D t p htD n
  dsimp only
  intro r y hy
  have hm := maximalIdeal_map_le_of_finite_of_injective D (StageAlgebra A D t p n)
    (stageAlgebra_algebraMap_injective A D t p n)
  have haStage : algebraMap D (StageAlgebra A D t p n) a ∈ maximalIdeal (StageAlgebra A D t p n) :=
    hm (Ideal.mem_map_of_mem (algebraMap D (StageAlgebra A D t p n)) haM)
  exact exists_same_span_with_regular_last y hy _ haStage
    (isSMulRegular_stageAlgebra_of_regular_D A D t p n a ha)

/-- 零化冪として正の指数を選べば、その冪についても同じパラメータ変更を適用できる。 -/
theorem stage_parameter_change_of_regular_D_pow
    (htD : ∀ i, algebraMap A D (t i) ∈ maximalIdeal D)
    (n : ℕ) (a : D) (haM : a ∈ maximalIdeal D) (ha : IsSMulRegular D a)
    (N : ℕ) (hN : 0 < N) :
    let _ := stageAlgebra_isLocalRing A D t p htD n
    ∀ {r : ℕ} (y : Fin (r + 1) → StageAlgebra A D t p n),
      IsSystemOfParameters (StageAlgebra A D t p n) y →
      ∃ y' : Fin (r + 1) → StageAlgebra A D t p n,
        Ideal.span (Set.range y') = Ideal.span (Set.range y) ∧
        IsSystemOfParameters (StageAlgebra A D t p n)
          (Fin.snoc (Fin.init y') ((algebraMap D (StageAlgebra A D t p n) a) ^ N)) := by
  let := stageAlgebra_isLocalRing A D t p htD n
  dsimp only
  intro r y hy
  simpa only [map_pow] using stage_parameter_change_of_regular_D A D t p htD n
    (a ^ N) (Ideal.pow_mem_of_mem _ haM N hN) (ha.pow N) y hy

/-- 有限段の列の変更と最後の正の冪の選択を、同じ生成イデアルの保存とともに供給する。 -/
theorem stage_parameter_power_selection_of_regular_D
    (htD : ∀ i, algebraMap A D (t i) ∈ maximalIdeal D)
    (n : ℕ) (a : D) (haM : a ∈ maximalIdeal D) (ha : IsSMulRegular D a) :
    let _ := stageAlgebra_isLocalRing A D t p htD n
    ∀ {r : ℕ} (y : Fin (r + 1) → StageAlgebra A D t p n),
      IsSystemOfParameters (StageAlgebra A D t p n) y →
      ∃ (y' : Fin (r + 1) → StageAlgebra A D t p n) (k : ℕ),
        Ideal.span (Set.range y') = Ideal.span (Set.range y) ∧ 0 < k ∧
        IsSystemOfParameters (StageAlgebra A D t p n)
          (Fin.snoc (Fin.init y') (y' (Fin.last r) ^ k)) ∧
        y' (Fin.last r) ^ k ∈ Ideal.span (Set.range (Fin.init y')) ⊔
          Ideal.span {algebraMap D (StageAlgebra A D t p n) a} := by
  let := stageAlgebra_isLocalRing A D t p htD n
  dsimp only
  intro r y hy
  have hm := maximalIdeal_map_le_of_finite_of_injective D (StageAlgebra A D t p n)
    (stageAlgebra_algebraMap_injective A D t p n)
  exact exists_same_span_parameters_with_last_pow_mem y hy _
    (hm (Ideal.mem_map_of_mem (algebraMap D (StageAlgebra A D t p n)) haM))
    (isSMulRegular_stageAlgebra_of_regular_D A D t p n a ha)

end SerrePositivity.CLMST
