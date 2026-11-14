module

public import SerrePositivity.EInfinity.SimplexCuts.ColorRankIntervals

/-!
# 同じ切断区間の高さと色別順位

Berger–Fresse §2.2.3–6、M14 L12a の内側射影の証明分割。
元の色別位置集合の順位を、同じ区間の高さの差によって読む。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- C399：元の区間の順位の幅は高さの幅と等しい（BF §2.2.6）。 -/
lemma colorIntervalRank_width {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (a : Fin r) (p : Fin (m + 1)) (hp : v.val p = a) :
    (colorIntervalLast s v a p hp).val - (colorIntervalFirst s v a p hp).val =
      hi s p - lo s p := by
  have hc := colorIntervalRanks_card s v a p hp
  rw [colorIntervalRanks_eq_Icc s v a p hp, Fin.card_Icc, intervalPositions_card] at hc
  have ho := colorIntervalFirst_le_last s v a p hp
  have hv : (colorIntervalFirst s v a p hp).val ≤
      (colorIntervalLast s v a p hp).val := ho
  omega

/-- 元の区間の高さを、同じ色の頂点列の順位へ移す記法（BF §2.2.6）。 -/
def colorHeightRank {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (a : Fin r) (p : Fin (m + 1)) (hp : v.val p = a)
    (h : ℕ) (hl : lo s p ≤ h) (hr : h ≤ hi s p) : Fin (outputDegree s v a + 1) :=
  ⟨(colorIntervalFirst s v a p hp).val + (h - lo s p), by
    have hw := colorIntervalRank_width s v a p hp
    have ho : (colorIntervalFirst s v a p hp).val ≤
        (colorIntervalLast s v a p hp).val := colorIntervalFirst_le_last s v a p hp
    have hb := (colorIntervalLast s v a p hp).isLt
    omega⟩

/-- C400：読み取った順位は元の同じ区間に属する（BF §2.2.6）。 -/
lemma colorHeightRank_mem {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (a : Fin r) (p : Fin (m + 1)) (hp : v.val p = a)
    (h : ℕ) (hl : lo s p ≤ h) (hr : h ≤ hi s p) :
    colorHeightRank s v a p hp h hl hr ∈ colorIntervalRanks s v a p := by
  rw [colorIntervalRanks_eq_Icc s v a p hp]
  apply Finset.mem_Icc.mpr
  have hw := colorIntervalRank_width s v a p hp
  have ho : (colorIntervalFirst s v a p hp).val ≤
      (colorIntervalLast s v a p hp).val := colorIntervalFirst_le_last s v a p hp
  constructor
  · change (colorIntervalFirst s v a p hp).val ≤
      (colorIntervalFirst s v a p hp).val + (h - lo s p)
    omega
  · change (colorIntervalFirst s v a p hp).val + (h - lo s p) ≤
      (colorIntervalLast s v a p hp).val
    omega

/-- C401：同じ元の区間内で高さを進めても順位は戻らない（BF §2.2.6）。 -/
lemma colorHeightRank_monotone {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (a : Fin r) (p : Fin (m + 1)) (hp : v.val p = a)
    (h h' : ℕ) (hl : lo s p ≤ h) (hr : h ≤ hi s p)
    (hl' : lo s p ≤ h') (hr' : h' ≤ hi s p) (hh : h ≤ h') :
    colorHeightRank s v a p hp h hl hr ≤ colorHeightRank s v a p hp h' hl' hr' := by
  change (colorIntervalFirst s v a p hp).val + (h - lo s p) ≤
    (colorIntervalFirst s v a p hp).val + (h' - lo s p)
  omega

/-- C402：元の両端の高さは、同じ区間の最初・最後の順位（BF §2.2.6）。 -/
lemma colorHeightRank_endpoints {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (a : Fin r) (p : Fin (m + 1)) (hp : v.val p = a) :
    colorHeightRank s v a p hp (lo s p) le_rfl (lo_le_hi s p) =
        colorIntervalFirst s v a p hp ∧
      colorHeightRank s v a p hp (hi s p) (lo_le_hi s p) le_rfl =
        colorIntervalLast s v a p hp := by
  have hw := colorIntervalRank_width s v a p hp
  have ho : (colorIntervalFirst s v a p hp).val ≤
      (colorIntervalLast s v a p hp).val := colorIntervalFirst_le_last s v a p hp
  constructor <;> apply Fin.ext
  · change (colorIntervalFirst s v a p hp).val + (lo s p - lo s p) = _
    omega
  · change (colorIntervalFirst s v a p hp).val + (hi s p - lo s p) = _
    omega

end SerrePositivity.EInfinity.SimplexCuts
