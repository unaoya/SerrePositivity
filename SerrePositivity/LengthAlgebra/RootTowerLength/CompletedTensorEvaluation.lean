module

public import SerrePositivity.LengthAlgebra.RootTowerLength.CompletedNormalized
public import SerrePositivity.CommutativeAlgebra.Adic.Completion.Tensor
public import SerrePositivity.CommutativeAlgebra.Length.Basic

/-! # 有限段から完備塔へ移した加群の長さ

有限長の段加群は p のある冪で消えるため、完備化による基底変更を未完備塔への
基底変更と同定できる。完備塔の Noether 性を仮定せず、証明済みの有限段の
正規化長さの公式をそのまま完備塔へ移す。
-/

@[expose] public noncomputable section
universe u
open scoped TensorProduct ENNReal
namespace SerrePositivity.RootTowerLength
open Section2 IsLocalRing TensorProduct
set_option backward.isDefEq.respectTransparency false

variable (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {h : ℕ} (t : Fin h → A) (p : ℕ) [Fact p.Prime]
    (ht : ∀ i, t i ∈ maximalIdeal A) (hp : (p : A) ∈ maximalIdeal A)

/-- 有限段の完備塔上の作用は、標準代数構造から得られる加群構造に固定する。 -/
local instance completedStageModule (n : ℕ) :
    Module (TowerStage A t p n) (CompletedTower A t p) := Algebra.toModule

omit [IsNoetherianRing A] in
include ht hp in
/-- 有限長の段加群を塔へ移すと、p のある冪で零化される。 -/
theorem exists_isTorsionBySet_p_pow_tensor (n : ℕ) (V : Type u) [AddCommGroup V]
    [Module (TowerStage A t p n) V] (hV : IsFiniteLength (TowerStage A t p n) V) :
    ∃ k : ℕ, Module.IsTorsionBySet (Tower A t p)
      (Tower A t p ⊗[TowerStage A t p n] V)
      ((Ideal.span {(p : Tower A t p)}) ^ k : Ideal (Tower A t p)) := by
  let B := TowerStage A t p n
  let S := Tower A t p
  let : IsLocalRing B := isLocalRing_towerStage A t p ht n
  obtain ⟨k, hk⟩ := SerrePositivity.IsFiniteLength.exists_isTorsionBySet_maximalIdeal_pow hV
  have hpB : (p : B) ∈ maximalIdeal B := by
    apply (le_of_isMaximal_towerStage A t p ht n (maximalIdeal B)).1
    simpa using Ideal.mem_map_of_mem (algebraMap A B) hp
  have hv : ∀ v : V, (p : B) ^ k • v = 0 := fun v =>
    hk (x := v) (a := ⟨_, Ideal.pow_mem_pow hpB k⟩)
  refine ⟨k, ?_⟩
  rw [Ideal.span_singleton_pow, Module.isTorsionBySet_span_singleton_iff]
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul s v =>
    have he : (p : S) ^ k = algebraMap B S ((p : B) ^ k) := by simp
    rw [he, smul_tmul', algebraMap_smul S ((p : B) ^ k), smul_tmul, hv, tmul_zero]
  | add x y hx hy => rw [smul_add, hx, hy, add_zero]

include hp in
/-- 完備塔からの係数制限で測る有限段加群の長さは、通常の段長さを段の階数で割った値。 -/
theorem completedNormalizedLength_tensor_eq_length (n : ℕ) (V : Type u)
    [AddCommGroup V] [Module (TowerStage A t p n) V]
    (hV : IsFiniteLength (TowerStage A t p n) V) :
    (completedNormalizedLength A t p ht).len
      (CompletedTower A t p ⊗[TowerStage A t p n] V) =
      (Module.length (TowerStage A t p n) V : ℝ≥0∞) /
        (stageRank h p n : ℝ≥0∞) := by
  let B := TowerStage A t p n
  let S := Tower A t p
  let C := CompletedTower A t p
  let W := S ⊗[B] V
  let Q := C ⊗[B] V
  obtain ⟨k, hk⟩ := exists_isTorsionBySet_p_pow_tensor A t p ht hp n V hV
  let E₁ : C ⊗[S] W ≃ₗ[C] Q :=
    AlgebraTensorModule.cancelBaseChange B S C C V
  let : Module S Q := Module.compHom Q (algebraMap S C)
  let : IsScalarTower S C Q := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let E : Q ≃ₗ[S] W := (E₁.symm.restrictScalars S).trans
    (adicCompletionTorsionTensorEquiv (Ideal.span {(p : S)})
      (Submodule.fg_span_singleton _) k hk)
  rw [completedNormalizedLength_len]
  change towerLengthFun A t p Q = _
  rw [towerLengthFun_congr E]
  exact towerLengthFun_tensor_eq_length A t p ht n V hV

end SerrePositivity.RootTowerLength
