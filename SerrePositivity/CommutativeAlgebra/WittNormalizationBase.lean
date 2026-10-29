module

public import SerrePositivity.CommutativeAlgebra.PowerSeries.Dimension
public import SerrePositivity.CommutativeAlgebra.PowerSeries.Completeness
public import Mathlib.Data.Fintype.Card
public import SerrePositivity.CommutativeAlgebra.WittPowerSeries

/-! # 混標数正規化に用いる具体的なWitt冪級数基底

引用3と同じ変数集合で、pと残りの変数をFin hで並べる。
極大イデアル生成と次元を実際の冪級数環について供給する。
-/

public section
namespace SerrePositivity
open IsLocalRing

/-- 零の座標をp、非零の座標を対応する形式変数とする標準列。 -/
noncomputable def wittPowerSeriesParameter {h : ℕ} (k : Type*) [CommRing k]
    (p : ℕ) [Fact p.Prime] (i : Fin h) :
    MvPowerSeries {j : Fin h // (j : ℕ) ≠ 0} (WittVector p k) :=
  if hi : (i : ℕ) = 0 then (p : _) else MvPowerSeries.X ⟨i, hi⟩

@[simp] theorem wittPowerSeriesParameter_zero {h : ℕ} (hpos : 0 < h)
    (k : Type*) [CommRing k] (p : ℕ) [Fact p.Prime] :
    wittPowerSeriesParameter k p ⟨0, hpos⟩ = (p : _) := by
  simp [wittPowerSeriesParameter]

@[simp] theorem wittPowerSeriesParameter_nonzero {h : ℕ}
    (k : Type*) [CommRing k] (p : ℕ) [Fact p.Prime] (i : Fin h) (hi : (i : ℕ) ≠ 0) :
    wittPowerSeriesParameter k p i = MvPowerSeries.X ⟨i, hi⟩ := by
  simp [wittPowerSeriesParameter, hi]

/-- h>0なら標準列の像はpと全変数からなる。 -/
theorem range_wittPowerSeriesParameter {h : ℕ} (hpos : 0 < h)
    (k : Type*) [CommRing k] (p : ℕ) [Fact p.Prime] :
    Set.range (wittPowerSeriesParameter (h := h) k p) =
      insert (p : MvPowerSeries {j : Fin h // (j : ℕ) ≠ 0} (WittVector p k))
        (Set.range MvPowerSeries.X) := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    by_cases hi : (i : ℕ) = 0
    · simp [wittPowerSeriesParameter, hi]
    · exact Set.mem_insert_of_mem _ ⟨⟨i, hi⟩, (wittPowerSeriesParameter_nonzero k p i hi).symm⟩
  · intro hx
    rcases hx with hx | ⟨i, hi⟩
    · exact ⟨⟨0, hpos⟩, (wittPowerSeriesParameter_zero hpos k p).trans hx.symm⟩
    · exact ⟨i.val, (wittPowerSeriesParameter_nonzero k p i.val i.property).trans hi⟩

/-- 標準列は実際のWitt冪級数環の極大イデアルを生成する。 -/
theorem span_wittPowerSeriesParameter_eq_maximalIdeal {h : ℕ} (hpos : 0 < h)
    (k : Type*) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectField k] :
    Ideal.span (Set.range (wittPowerSeriesParameter (h := h) k p)) =
      maximalIdeal (MvPowerSeries {j : Fin h // (j : ℕ) ≠ 0} (WittVector p k)) := by
  rw [range_wittPowerSeriesParameter hpos, Ideal.span_insert, wittPowerSeries_maximalIdeal_eq]

/-- 引用3で使う変数集合の個数はh-1。 -/
theorem card_nonzeroFin {h : ℕ} (hpos : 0 < h) :
    Fintype.card {i : Fin h // (i : ℕ) ≠ 0} = h - 1 := by
  have h0 : Fintype.card {i : Fin h // (i : ℕ) = 0} = 1 := by
    let e : {i : Fin h // (i : ℕ) = 0} ≃ {i : Fin h // i = ⟨0, hpos⟩} :=
      Equiv.subtypeEquivRight (fun i ↦ by simp only [Fin.ext_iff])
    exact (Fintype.card_congr e).trans (Fintype.card_subtype_eq _)
  rw [Fintype.card_subtype_compl (fun i : Fin h ↦ (i : ℕ) = 0), Fintype.card_fin, h0]

/-- 引用3と同じ変数集合の標準Witt冪級数基底の次元はh。 -/
theorem ringKrullDim_wittNormalizationBase {h : ℕ} (hpos : 0 < h)
    (k : Type*) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectField k] :
    ringKrullDim (MvPowerSeries {i : Fin h // (i : ℕ) ≠ 0} (WittVector p k)) = h := by
  rw [ringKrullDim_wittPowerSeries, card_nonzeroFin hpos]
  have hn : 1 + (h - 1) = h := by omega
  exact_mod_cast hn

/-- h=1の基底は空変数の冪級数環であり、Witt係数環へ明示的に同型。 -/
noncomputable def wittNormalizationBase_one_equiv
    (k : Type*) [CommRing k] (p : ℕ) [Fact p.Prime] :
    MvPowerSeries {i : Fin 1 // (i : ℕ) ≠ 0} (WittVector p k) ≃+* WittVector p k := by
  let : IsEmpty {i : Fin 1 // (i : ℕ) ≠ 0} :=
    (Fintype.card_eq_zero_iff).mp (by simp)
  exact (MvPowerSeries.isEmptyEquiv _ (WittVector p k)).toRingEquiv

end SerrePositivity
