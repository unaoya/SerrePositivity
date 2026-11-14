module

public import SerrePositivity.EInfinity.SimplexCuts.IntervalSingletons
public import Mathlib.Order.Interval.Finset.Fin

/-!
# 切断区間の頂点数と幾何学的長さ

Berger–Fresse §2.2.3–4、M14 L09a。
水平座標のfiberは連続した位置の区間で、頂点数は垂直座標の両端の差に一を足した値。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- C91：区間の位置のfiberは、定義した最小位置と最大位置の閉区間。 -/
lemma intervalPositions_eq_Icc {m q : ℕ} (s : Cut m q) (i : Fin (m + 1)) :
    intervalPositions s i = Finset.Icc
      ((intervalPositions s i).min' (intervalPositions_nonempty s i))
      ((intervalPositions s i).max' (intervalPositions_nonempty s i)) := by
  ext j
  constructor
  · intro hj
    exact Finset.mem_Icc.mpr
      ⟨(intervalPositions s i).min'_le j hj, (intervalPositions s i).le_max' j hj⟩
  · intro hj
    obtain ⟨hl, hr⟩ := Finset.mem_Icc.mp hj
    have h₁ := s.horizontal.monotone hl
    have h₂ := s.horizontal.monotone hr
    rw [horizontal_lo_vertex] at h₁
    rw [horizontal_hi_vertex] at h₂
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_antisymm h₂ h₁⟩

/-- C92：区間の頂点数は幾何学的長さに一を足した値。 -/
lemma intervalPositions_card {m q : ℕ} (s : Cut m q) (i : Fin (m + 1)) :
    (intervalPositions s i).card = hi s i - lo s i + 1 := by
  have h₀ := s.coordinate_sum
    ((intervalPositions s i).min' (intervalPositions_nonempty s i))
  have h₁ := s.coordinate_sum
    ((intervalPositions s i).max' (intervalPositions_nonempty s i))
  rw [horizontal_lo_vertex] at h₀
  rw [horizontal_hi_vertex] at h₁
  have hle := lo_le_hi s i
  rw [intervalPositions_eq_Icc, Fin.card_Icc]
  change _ = hi s i - lo s i + 1
  change i.val + lo s i = _ at h₀
  change i.val + hi s i = _ at h₁
  omega

end SerrePositivity.EInfinity.SimplexCuts
