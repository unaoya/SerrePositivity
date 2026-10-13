module

public import SerrePositivity.LengthAlgebra.RootTowerLength.FiniteStage
public import SerrePositivity.Paper.Section2.TowerLength

/-!
# λ∞ の有限段公式への有限生成一致の適用

有限表示の降下、λ* の有限段公式、係数拡大の冪ねじれは
`LengthAlgebra/RootTowerLength/FiniteStage.lean` に抽出した。
ここには、C1（有限生成加群で λ∞ = λ*）を使う二つの有限段公式を残す。
宣言名・仮定・結論を保持し、証明済み C1 を適用する。
-/

@[expose] public section

universe u

open IsLocalRing TensorProduct
open scoped ENNReal

namespace SerrePositivity
namespace Section2

variable (A : Type u) [CommRing A] {h : ℕ} (t : Fin h → A) (p : ℕ)

section formula2
variable [IsLocalRing A]

variable [IsNoetherianRing A] [Fact p.Prime] (ht : ∀ i, t i ∈ maximalIdeal A)

set_option linter.style.haveILetI false in
include ht in
/-- **(2.2) 有限段の公式**：`λ_∞(Λ ⊗_{A_n} V) = ℓ_{A_n}(V) / p^{nh}`。(C1) と (S1) から。 -/
theorem towerLengthFun_tensor (n : ℕ) (V : Type u) [AddCommGroup V]
    [Module (TowerStage A t p n) V] (hV : IsFiniteLength (TowerStage A t p n) V)
    (hVt : IsPowTorsion ((maximalIdeal A).map (algebraMap A (TowerStage A t p n))) V) :
    towerLengthFun A t p (Tower A t p ⊗[TowerStage A t p n] V) =
      (Module.length (TowerStage A t p n) V : ℝ≥0∞) / (stageRank h p n : ℝ≥0∞) := by
  haveI : IsNoetherian (TowerStage A t p n) V :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hV).1
  rw [towerLengthFun_eq_fgLength A t p ht _ (isPowTorsion_tower_tensor A t p n V hVt),
    fgLength_tensor A t p ht n V hV]

include ht in
/-- 有限長の段加群では、有限段の公式の冪ねじれ条件は自動的に満たされる。
極大イデアルのある冪が加群を消し、基底の極大イデアルの像はその極大イデアルに入る。 -/
theorem towerLengthFun_tensor_of_finiteLength (n : ℕ) (V : Type u) [AddCommGroup V]
    [Module (TowerStage A t p n) V] (hV : IsFiniteLength (TowerStage A t p n) V) :
    towerLengthFun A t p (Tower A t p ⊗[TowerStage A t p n] V) =
      (Module.length (TowerStage A t p n) V : ℝ≥0∞) / (stageRank h p n : ℝ≥0∞) := by
  let := isLocalRing_towerStage A t p ht n
  apply towerLengthFun_tensor A t p ht n V hV
  obtain ⟨k, hk⟩ := IsFiniteLength.exists_isTorsionBySet_maximalIdeal_pow hV
  refine ⟨k, ?_⟩
  rw [Module.isTorsionBySet_iff_subset_annihilator] at hk ⊢
  exact (pow_le_pow_left'
    (le_of_isMaximal_towerStage A t p ht n (maximalIdeal (TowerStage A t p n))).1 k).trans hk

end formula2

end Section2

end SerrePositivity
