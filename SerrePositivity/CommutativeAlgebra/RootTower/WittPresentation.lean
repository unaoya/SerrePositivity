module

public import SerrePositivity.CommutativeAlgebra.RootTower.FrobeniusKernel
public import SerrePositivity.CommutativeAlgebra.PowerSeries.Completeness
public import SerrePositivity.CommutativeAlgebra.PowerSeries.Dimension
public import SerrePositivity.CommutativeAlgebra.WittPowerSeries

/-! # Witt係数の標準表示から完備塔のperfectoid性を証明する

表示からp正則性、局所性、次元、極大イデアルの生成を供給する。
原典の非零座標の添字も有限型の座標へ移す。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.Section2
open IsLocalRing
variable (A k : Type u) [CommRing A] [Field k] (p : ℕ)
    [Fact p.Prime] [CharP k p] [PerfectField k]

/-- 標準Witt係数表示から、追加の局所環・次元の仮定なしにperfectoid性を証明する。 -/
theorem completedTower_isIntegralPerfectoid_of_wittPresentation
    {r : ℕ} (t : Fin (r + 1) → A) (hti : t 0 = (p : A))
    (e : A ≃+* MvPowerSeries (Fin r) (WittVector p k))
    (he : ∀ i : Fin r, e (t i.succ) = MvPowerSeries.X i) :
    IsIntegralPerfectoid (CompletedTower A t p) p := by
  let B := MvPowerSeries (Fin r) (WittVector p k)
  let : IsLocalRing A := e.symm.isLocalRing
  let : IsNoetherianRing A := isNoetherianRing_of_ringEquiv B e.symm
  let : IsDomain A := e.toMulEquiv.isDomain B
  have hp0 : (p : A) ≠ 0 := by
    intro hp
    have hh := congrArg (fun a : A ↦ MvPowerSeries.constantCoeff (e a)) hp
    simp only [map_natCast, map_zero] at hh
    exact WittVector.p_nonzero p k hh
  have hp : IsSMulRegular A (p : A) := (IsRegular.of_ne_zero hp0).left.isSMulRegular
  have hdim : ringKrullDim A = r + 1 := by
    rw [RingEquiv.ringKrullDim e]
    simpa only [Fintype.card_fin, add_comm] using ringKrullDim_wittPowerSeries (Fin r) k p
  have ht : Ideal.span (Set.range t) = maximalIdeal A := by
    apply (Ideal.comap_injective_of_surjective e.symm.toRingHom e.symm.surjective)
    change (Ideal.span (Set.range t)).comap e.symm = (maximalIdeal A).comap e.symm
    simp only [Ideal.comap_symm]
    rw [Ideal.map_span, map_ringEquiv_maximalIdeal, wittPowerSeries_maximalIdeal_eq]
    have hset : e '' Set.range t = {(p : B)} ∪ Set.range (MvPowerSeries.X (σ := Fin r)
        (R := WittVector p k)) := by
      ext x
      constructor
      · rintro ⟨a, ⟨i, rfl⟩, rfl⟩
        refine Fin.cases ?_ (fun j ↦ ?_) i
        · left; simp [hti]
        · right; exact ⟨j, (he j).symm⟩
      · rintro (hx | ⟨i, rfl⟩)
        · refine ⟨t 0, Set.mem_range_self _, ?_⟩
          have hx' : x = (p : B) := hx
          simpa only [hti, map_natCast] using hx'.symm
        · exact ⟨t i.succ, Set.mem_range_self _, he i⟩
    rw [hset, Ideal.span_union]
  exact completedTower_isIntegralPerfectoid_of_wittPresentation_and_parameters A p t k
    hp ht hti hdim e he

/-- 零番以外の座標の添字を、順序を保ったFin rへ移す。 -/
def nonzeroCoordinateEquiv (r : ℕ) : {i : Fin (r + 1) // (i : ℕ) ≠ 0} ≃ Fin r where
  toFun i := ⟨(i.val : ℕ) - 1, by have := i.val.isLt; have := i.property; omega⟩
  invFun i := ⟨i.succ, by simp⟩
  left_inv i := by
    apply Subtype.ext
    apply Fin.ext
    have := i.property
    simp only [Fin.val_succ]
    omega
  right_inv i := by apply Fin.ext; simp

/-- 原典の添字と同じ標準Witt係数表示から、完備塔のperfectoid性を証明する。 -/
theorem completedTower_isIntegralPerfectoid_of_standard_wittPresentation
    {h : ℕ} (t : Fin h → A) (hpos : 0 < h) (hti : t ⟨0, hpos⟩ = (p : A))
    (e : A ≃+* MvPowerSeries {i : Fin h // (i : ℕ) ≠ 0} (WittVector p k))
    (he : ∀ i hi, e (t i) = MvPowerSeries.X ⟨i, hi⟩) :
    IsIntegralPerfectoid (CompletedTower A t p) p := by
  cases h with
  | zero => omega
  | succ r =>
    let e' := e.trans (MvPowerSeries.renameEquiv (WittVector p k)
      (nonzeroCoordinateEquiv r)).toRingEquiv
    apply completedTower_isIntegralPerfectoid_of_wittPresentation A k p t hti e'
    intro i
    change MvPowerSeries.rename (nonzeroCoordinateEquiv r) (e (t i.succ)) = _
    rw [he i.succ (by simp), MvPowerSeries.rename_X]
    congr 1

end SerrePositivity.Section2
