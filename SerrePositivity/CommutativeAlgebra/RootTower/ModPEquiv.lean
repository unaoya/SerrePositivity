module

public import SerrePositivity.CommutativeAlgebra.RootTower.ModPSurjectivity
public import SerrePositivity.CommutativeAlgebra.RootTower.ModPInjectivity
public import SerrePositivity.CommutativeAlgebra.PowerSeries.Basic
public import SerrePositivity.CommutativeAlgebra.Witt.PowerSeries

/-! # 有限段のp冪根による商とmod pの具体的同型

全射性は冪級数の剰余分解、単射性は正則局所環の商の整域性と整拡大から得る。
この同型は基底環Aの作用をFrobeniusでねじる環同型であり、A代数同型ではない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.Section2
open IsLocalRing
variable (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {r : ℕ} (t : Fin (r + 1) → A) (p : ℕ) [Fact p.Prime]
    [CharP (A ⧸ Ideal.span {(p : A)}) p]

/-- 最小パラメータ系とmod pの冪級数表示から、実際のFrobenius商射は全単射。 -/
theorem stageRootModPFrobenius_bijective_of_powerSeries
    {k σ : Type*} [CommRing k] [Finite σ] [CharP k p] [PerfectRing k p]
    (ht : Ideal.span (Set.range t) = maximalIdeal A) (htp : t 0 = (p : A))
    (hdim : ringKrullDim A = r + 1)
    (e : A ⧸ Ideal.span {(p : A)} ≃+* MvPowerSeries σ k) (ι : σ → Fin (r + 1))
    (he : ∀ i, e (Ideal.Quotient.mk (Ideal.span {(p : A)}) (t (ι i))) = MvPowerSeries.X i)
    (n : ℕ) : Function.Bijective (stageRootModPFrobenius A t p n 0 htp) := by
  let : IsDomain (TowerStage A t p n ⧸ Ideal.span {stageX A t p n 0}) :=
    stageRootQuotient_isDomain_of_parameters A p t ht hdim n
  have hQ := isRegularLocalRing_quotient_head_and_dim t ht hdim
  rw [htp] at hQ
  let : IsRegularLocalRing (A ⧸ Ideal.span {(p : A)}) := hQ.1
  obtain ⟨rs, hreg, hgen, _⟩ := exists_regular_generators (A ⧸ Ideal.span {(p : A)})
  let : IsDomain (A ⧸ Ideal.span {(p : A)}) := isDomain_of_regular_generators rs hreg hgen
  exact ⟨stageRootModPFrobenius_injective_of_isDomain A t p n 0 htp,
    stageRootModPFrobenius_surjective_of_powerSeries t p e ι he n 0 htp⟩

/-- pの根を零にした有限段の商からA/pへのFrobenius環同型。 -/
def stageRootModPFrobeniusEquiv
    {k σ : Type*} [CommRing k] [Finite σ] [CharP k p] [PerfectRing k p]
    (ht : Ideal.span (Set.range t) = maximalIdeal A) (htp : t 0 = (p : A))
    (hdim : ringKrullDim A = r + 1)
    (e : A ⧸ Ideal.span {(p : A)} ≃+* MvPowerSeries σ k) (ι : σ → Fin (r + 1))
    (he : ∀ i, e (Ideal.Quotient.mk (Ideal.span {(p : A)}) (t (ι i))) = MvPowerSeries.X i)
    (n : ℕ) : TowerStage A t p n ⧸ Ideal.span {stageX A t p n 0} ≃+*
      A ⧸ Ideal.span {(p : A)} :=
  RingEquiv.ofBijective (stageRootModPFrobenius A t p n 0 htp)
    (stageRootModPFrobenius_bijective_of_powerSeries A t p ht htp hdim e ι he n)

@[simp] theorem stageRootModPFrobeniusEquiv_mk
    {k σ : Type*} [CommRing k] [Finite σ] [CharP k p] [PerfectRing k p]
    (ht : Ideal.span (Set.range t) = maximalIdeal A) (htp : t 0 = (p : A))
    (hdim : ringKrullDim A = r + 1)
    (e : A ⧸ Ideal.span {(p : A)} ≃+* MvPowerSeries σ k) (ι : σ → Fin (r + 1))
    (he : ∀ i, e (Ideal.Quotient.mk (Ideal.span {(p : A)}) (t (ι i))) = MvPowerSeries.X i)
    (n : ℕ) (z : TowerStage A t p n) :
    stageRootModPFrobeniusEquiv A t p ht htp hdim e ι he n (Ideal.Quotient.mk _ z) =
      stageModPFrobenius A t p n z := rfl

/-- Witt係数冪級数の標準表示から得る有限段Frobenius商同型。
表示の存在を引用することと、この表示から同型を証明することを分離する。 -/
def stageRootModPFrobeniusEquiv_of_wittPowerSeries
    (k : Type u) [CommRing k] [CharP k p] [PerfectRing k p]
    (ht : Ideal.span (Set.range t) = maximalIdeal A) (htp : t 0 = (p : A))
    (hdim : ringKrullDim A = r + 1)
    (e : A ≃+* MvPowerSeries (Fin r) (WittVector p k))
    (he : ∀ i : Fin r, e (t i.succ) = MvPowerSeries.X i) (n : ℕ) :
    TowerStage A t p n ⧸ Ideal.span {stageX A t p n 0} ≃+*
      A ⧸ Ideal.span {(p : A)} :=
  stageRootModPFrobeniusEquiv A t p ht htp hdim
    (wittPresentedModPEquiv A (Fin r) k p e) Fin.succ
    (fun i ↦ wittPresentedModPEquiv_coordinate A (Fin r) k p e (t i.succ) i (he i)) n

@[simp] theorem stageRootModPFrobeniusEquiv_of_wittPowerSeries_mk
    (k : Type u) [CommRing k] [CharP k p] [PerfectRing k p]
    (ht : Ideal.span (Set.range t) = maximalIdeal A) (htp : t 0 = (p : A))
    (hdim : ringKrullDim A = r + 1)
    (e : A ≃+* MvPowerSeries (Fin r) (WittVector p k))
    (he : ∀ i : Fin r, e (t i.succ) = MvPowerSeries.X i)
    (n : ℕ) (z : TowerStage A t p n) :
    stageRootModPFrobeniusEquiv_of_wittPowerSeries A t p k ht htp hdim e he n
      (Ideal.Quotient.mk _ z) = stageModPFrobenius A t p n z := rfl

end SerrePositivity.Section2
