module

public import SerrePositivity.CommutativeAlgebra.RootTower.ModP
public import SerrePositivity.CLMST.StageModPImageLength

/-! # 実際の有限段商の低次元長さ上界

像の商に対して先に証明した成長評価を、具体的なFrobenius商同型を通じて源へ移す。
この段階の上界は先頭の根そのもので割った商についてのものであり、
より低い段の根の冪で割る場合には別のフィルトレーション倍率が必要である。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.CLMST
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

end SerrePositivity.CLMST
