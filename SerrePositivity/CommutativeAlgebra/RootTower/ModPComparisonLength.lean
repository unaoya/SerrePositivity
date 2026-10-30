module

public import SerrePositivity.CommutativeAlgebra.RootTower.ModPEquiv
public import SerrePositivity.CommutativeAlgebra.Length.Basic

/-! # 有限段Frobenius比較による通常の長さの一致

先頭の根を含むイデアルで割った有限段の通常の長さを、A/pの像イデアルによる
商の通常の長さへ移す。共通のA作用に関する線形性を誤って用いない。
-/

@[expose] public noncomputable section
namespace SerrePositivity.Section2
open IsLocalRing
variable (A : Type*) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {r : ℕ} (t : Fin (r + 1) → A) (p : ℕ) [Fact p.Prime]
    [CharP (A ⧸ Ideal.span {(p : A)}) p]

/-- 実際のFrobenius射により、根を含む任意の商の長さが像の商の長さに一致する。 -/
theorem length_stage_quotient_eq_modP_image
    {k σ : Type*} [CommRing k] [Finite σ] [CharP k p] [PerfectRing k p]
    (ht : Ideal.span (Set.range t) = maximalIdeal A) (htp : t 0 = (p : A))
    (hdim : ringKrullDim A = r + 1)
    (e : A ⧸ Ideal.span {(p : A)} ≃+* MvPowerSeries σ k) (ι : σ → Fin (r + 1))
    (he : ∀ i, e (Ideal.Quotient.mk (Ideal.span {(p : A)}) (t (ι i))) = MvPowerSeries.X i)
    (n : ℕ) (I : Ideal (TowerStage A t p n))
    (hI : Ideal.span {stageX A t p n 0} ≤ I) :
    Module.length (TowerStage A t p n) (TowerStage A t p n ⧸ I) =
      Module.length (A ⧸ Ideal.span {(p : A)})
        ((A ⧸ Ideal.span {(p : A)}) ⧸ I.map (stageModPFrobenius A t p n)) := by
  have hf := stageRootModPFrobenius_bijective_of_powerSeries A t p ht htp hdim e ι he n
  apply length_quotient_eq_image_of_surjective _
    (stageModPFrobenius_surjective_of_powerSeries t p e ι he n)
  rw [stageModPFrobenius_ker_of_quotient_injective A t p n 0 htp hf.1]
  exact hI

end SerrePositivity.Section2
