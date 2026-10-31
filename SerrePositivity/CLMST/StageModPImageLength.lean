module

public import SerrePositivity.CommutativeAlgebra.RootTower.ModP
public import SerrePositivity.CLMST.ModPHypersurfaceGrowth

/-! # 有限段の関係式のmod p像の通常長さ

実際のFrobenius射で有限段の三つの関係式を送り、その像の商の長さに
低次元成長評価を適用する。源への長さの移送と上界は、
射の全単射性を使う別モジュール `StageModPLengthBound` で証明する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.CLMST
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

end SerrePositivity.CLMST
