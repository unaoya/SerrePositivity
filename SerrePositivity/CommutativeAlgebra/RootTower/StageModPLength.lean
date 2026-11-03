module

public import SerrePositivity.CommutativeAlgebra.RootTower.ModP
public import SerrePositivity.CommutativeAlgebra.ModPHypersurfaceGrowth

/-! # 根の塔の有限段の商の mod p 長さの上界

## 概要

有限段の三つの関係式を Frobenius で送った像の商に、`A/(p, g)` の低次元の増大評価（CommutativeAlgebra/ModPHypersurfaceGrowth）を当てて長さの上界を得る（`exists_stage_modP_image_length_bound`）。具体的な Frobenius 商の同型を通じて、先頭の根で割った有限段の商へ上界を移す（`exists_stage_root_quotient_length_bound`）。

## 方針

像の商で評価してから、全単射な Frobenius 射で源へ移す。

## 規約

上界は先頭の根そのもので割った商についてのもので、低い段の根の冪で割る場合は別のフィルトレーションの倍率が要る。旧 `CLMST/StageModPImageLength`・`StageModPLengthBound`。

## 使われ方

CLMST の `CyclicLengthBound`（Prop 4.0.10）の正規化された長さの評価。
-/

@[expose] public noncomputable section

universe u

section StageModPImageLengthPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open IsLocalRing Section2

/-- 有限段の関係式を送ったmod p商の長さは、段の差の倍率を含む低次元上界を持つ。
射の像を計算して適用し、源の通常長さとの比較を仮定に埋め込まない。 -/
theorem exists_stage_modP_image_length_bound
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {r : ℕ} (t : Fin (r + 2) → A) (p : ℕ) [Fact p.Prime]
    (ht : Ideal.span (Set.range t) = maximalIdeal A) (htp : t 0 = (p : A))
    (hdim : ringKrullDim A = r + 2) (g : A)
    (hgm : g ∈ maximalIdeal A) (hpg : ¬ (p : A) ∣ g) :
    let Q := A ⧸ Ideal.span {(p : A)}
    letI : IsRegularLocalRing Q := (modP_regular_and_dim_of_parameters A t p ht htp hdim).1
    letI : CharP Q p := modP_charP_of_parameters A t p ht htp
    ∃ c : ℕ, ∀ (n m : ℕ) (_ : n ≤ m) (z : TowerStage A t p m),
      z ^ (p ^ n) - algebraMap A (TowerStage A t p m) g ∈
        Ideal.span {(p : TowerStage A t p m)} →
      Module.length Q (Q ⧸
        ((maximalIdeal A).map (algebraMap A (TowerStage A t p m)) ⊔
          Ideal.span {stageX A t p m 0 ^ (p ^ (m - n))} ⊔ Ideal.span {z}).map
            (stageModPFrobenius A t p m)) ≤
              ((p ^ (m - n) : ℕ) : ℕ∞) * (((p ^ m : ℕ) : ℕ∞) ^ r * (c : ℕ∞)) := by
  let Q := A ⧸ Ideal.span {(p : A)}
  have hQ := modP_regular_and_dim_of_parameters A t p ht htp hdim
  let : IsRegularLocalRing Q := hQ.1
  let : CharP Q p := modP_charP_of_parameters A t p ht htp
  let : IsDomain Q := modP_isDomain_of_parameters A t p ht htp hdim
  let q := Ideal.Quotient.mk (Ideal.span {(p : A)})
  have hgQ : q g ∈ maximalIdeal Q := by
    have hh := Ideal.mem_map_of_mem q hgm
    rwa [map_maximalIdeal_of_surjective q Ideal.Quotient.mk_surjective] at hh
  obtain ⟨c, hc⟩ := exists_frobenius_hypersurface_power_length_bound Q p (q g)
    (modP_image_mem_nonZeroDivisors_of_not_dvd A t p ht htp hdim g hpg) hgQ hQ.2
  refine ⟨c, fun n m hnm z hz ↦ ?_⟩
  have heq := stageModPFrobenius_map_root_power_relations A t p n m hnm 0 htp g z hz
  rw [(Ideal.quotientEquivAlgOfEq Q heq).toLinearEquiv.length_eq]
  exact hc m (p ^ (m - n))

end SerrePositivity

end StageModPImageLengthPart

section StageModPLengthBoundPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open IsLocalRing Section2

/-- mod pの冪級数表示の下で、源の有限段商にも低次元成長上界が成り立つ。 -/
theorem exists_stage_root_quotient_length_bound
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {r : ℕ} (t : Fin (r + 2) → A) (p : ℕ) [Fact p.Prime]
    (ht : Ideal.span (Set.range t) = maximalIdeal A) (htp : t 0 = (p : A))
    (hdim : ringKrullDim A = r + 2)
    {k σ : Type*} [CommRing k] [Finite σ] [CharP k p] [PerfectRing k p]
    (e : A ⧸ Ideal.span {(p : A)} ≃+* MvPowerSeries σ k) (ι : σ → Fin (r + 2))
    (he : ∀ i, e (Ideal.Quotient.mk (Ideal.span {(p : A)}) (t (ι i))) = MvPowerSeries.X i)
    (g : A) (hgm : g ∈ maximalIdeal A) (hpg : ¬ (p : A) ∣ g) :
    ∃ c : ℕ, ∀ (n m : ℕ) (_ : n ≤ m) (z : TowerStage A t p m),
      z ^ (p ^ n) - algebraMap A (TowerStage A t p m) g ∈
        Ideal.span {(p : TowerStage A t p m)} →
      Module.length (TowerStage A t p m) (TowerStage A t p m ⧸
        ((maximalIdeal A).map (algebraMap A (TowerStage A t p m)) ⊔
          Ideal.span {stageX A t p m 0} ⊔ Ideal.span {z})) ≤
        ((p ^ (m - n) : ℕ) : ℕ∞) * (((p ^ m : ℕ) : ℕ∞) ^ r * (c : ℕ∞)) := by
  let Q := A ⧸ Ideal.span {(p : A)}
  let : IsRegularLocalRing Q := (modP_regular_and_dim_of_parameters A t p ht htp hdim).1
  let : CharP Q p := modP_charP_of_parameters A t p ht htp
  let : IsDomain Q := modP_isDomain_of_parameters A t p ht htp hdim
  obtain ⟨c, hc⟩ := exists_stage_modP_image_length_bound A t p ht htp hdim g hgm hpg
  refine ⟨c, fun n m hnm z hz ↦ ?_⟩
  have hdim' : ringKrullDim A = (r + 1 : ℕ) + 1 := by
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using hdim
  rw [length_stage_quotient_eq_modP_image A t p ht htp hdim' e ι he m _
    (le_sup_of_le_left le_sup_right)]
  have himage :
      ((maximalIdeal A).map (algebraMap A (TowerStage A t p m)) ⊔
        Ideal.span {stageX A t p m 0} ⊔ Ideal.span {z}).map (stageModPFrobenius A t p m) =
      ((maximalIdeal A).map (algebraMap A (TowerStage A t p m)) ⊔
        Ideal.span {stageX A t p m 0 ^ (p ^ (m - n))} ⊔ Ideal.span {z}).map
          (stageModPFrobenius A t p m) := by
    rw [stageModPFrobenius_map_root_relations A t p n m hnm 0 htp g z hz,
      stageModPFrobenius_map_root_power_relations A t p n m hnm 0 htp g z hz]
  rw [(Ideal.quotientEquivAlgOfEq Q himage).toLinearEquiv.length_eq]
  exact hc n m hnm z hz

end SerrePositivity

end StageModPLengthBoundPart
