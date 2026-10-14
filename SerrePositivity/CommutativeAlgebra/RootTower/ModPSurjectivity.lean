module

public import SerrePositivity.CommutativeAlgebra.RootTower.ModPFrobenius
public import SerrePositivity.CommutativeAlgebra.PowerSeriesResidueDecomposition

/-! # 標準冪級数表示による有限段Frobenius射の全射性

mod p 商の冪級数表示と座標の一致を仮定し、具体的に定義した射の全射性を証明する。
Witt冪級数表示からこの仮定を得る部分は係数商の共通同型が担う。
-/

@[expose] public noncomputable section
namespace SerrePositivity.Section2
variable {A k σ : Type*} [CommRing A] [CommRing k] [Finite σ]
    {h : ℕ} (t : Fin h → A) (p : ℕ) [Fact p.Prime]
    [CharP k p] [PerfectRing k p] [CharP (A ⧸ Ideal.span {(p : A)}) p]

/-- mod p の座標冪級数表示があれば、有限段 Frobenius 射は全射。 -/
theorem stageModPFrobenius_surjective_of_powerSeries
    (e : A ⧸ Ideal.span {(p : A)} ≃+* MvPowerSeries σ k)
    (ι : σ → Fin h)
    (ht : ∀ i, e (Ideal.Quotient.mk (Ideal.span {(p : A)}) (t (ι i))) = MvPowerSeries.X i)
    (n : ℕ) : Function.Surjective (stageModPFrobenius A t p n) := by
  let f := e.toRingHom.comp (stageModPFrobenius A t p n)
  have hf : Function.Surjective f := by
    apply powerSeries_surjective_of_powers_and_variables p n
    · intro φ
      obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (e.symm φ)
      refine ⟨algebraMap A (TowerStage A t p n) a, ?_⟩
      change e (stageModPFrobenius A t p n (algebraMap A (TowerStage A t p n) a)) = _
      rw [stageModPFrobenius_algebraMap, map_pow, ha, e.apply_symm_apply]
    · intro i
      refine ⟨stageX A t p n (ι i), ?_⟩
      change e (stageModPFrobenius A t p n (stageX A t p n (ι i))) = _
      rw [stageModPFrobenius_stageX, ht]
  intro a
  obtain ⟨b, hb⟩ := hf (e a)
  exact ⟨b, e.injective hb⟩

/-- pの根を零にした商射も全射である。単射性は別途必要。 -/
theorem stageRootModPFrobenius_surjective_of_powerSeries
    (e : A ⧸ Ideal.span {(p : A)} ≃+* MvPowerSeries σ k)
    (ι : σ → Fin h)
    (ht : ∀ i, e (Ideal.Quotient.mk (Ideal.span {(p : A)}) (t (ι i))) = MvPowerSeries.X i)
    (n : ℕ) (j : Fin h) (htj : t j = (p : A)) :
    Function.Surjective (stageRootModPFrobenius A t p n j htj) := by
  intro a
  obtain ⟨b, hb⟩ := stageModPFrobenius_surjective_of_powerSeries t p e ι ht n a
  exact ⟨Ideal.Quotient.mk _ b, hb⟩

end SerrePositivity.Section2
