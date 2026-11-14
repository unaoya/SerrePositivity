module

public import SerrePositivity.EInfinity.SimplexCuts.IntervalSingletons
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleStepMembership

/-!
# 一頂点のfiberと隣接する二辺

Berger–Fresse §2.2.7、M14 L09a。
有限な単調写像のfiberが一頂点であることを、その直前直後の厳密な増分で判定する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- C54：水平辺への所属は水平座標が増える条件。 -/
lemma mem_iff_horizontal_lt {m q : ℕ} (s : Cut m q) (a : Fin (m + q)) :
    a ∈ s.val ↔ s.horizontal a.castSucc < s.horizontal a.succ := by
  constructor
  · intro h
    have hs := (s.step_of_mem a h).1
    change (s.horizontal a.castSucc).val < (s.horizontal a.succ).val
    omega
  · intro h
    by_contra hn
    rw [(s.step_of_notMem a hn).1] at h
    exact (lt_irrefl _) h

/-- C55：単調写像の一頂点のfiberは、両側の厳密な増分で特徴づけられる。 -/
lemma monotone_fiber_singleton_iff {N M : ℕ} (f : Fin (N + 1) →o Fin (M + 1))
    (k : Fin (N + 1)) :
    (∀ j, f j = f k → j = k) ↔
      (∀ a : Fin N, a.succ = k → f a.castSucc < f k) ∧
      (∀ a : Fin N, a.castSucc = k → f k < f a.succ) := by
  constructor
  · intro h
    constructor
    · intro a ha
      apply lt_of_le_of_ne (f.monotone (ha ▸ a.castSucc_le_succ))
      intro he
      have hk := h a.castSucc he
      have hv := congrArg Fin.val (hk.trans ha.symm)
      simp only [Fin.val_castSucc, Fin.val_succ] at hv
      omega
    · intro a ha
      apply lt_of_le_of_ne (f.monotone (ha ▸ a.castSucc_le_succ))
      intro he
      have hk := h a.succ he.symm
      have hv := congrArg Fin.val (hk.trans ha.symm)
      simp only [Fin.val_castSucc, Fin.val_succ] at hv
      omega
  · rintro ⟨hl, hr⟩ j hj
    apply Fin.ext
    by_contra hne
    by_cases hjk : j.val < k.val
    · let a : Fin N := ⟨k.val - 1, by have hk := k.isLt; omega⟩
      have ha : a.succ = k := by apply Fin.ext; change k.val - 1 + 1 = k.val; omega
      have hja : j ≤ a.castSucc := by change j.val ≤ k.val - 1; omega
      have hb := lt_of_le_of_lt (f.monotone hja) (hl a ha)
      rw [hj] at hb
      exact (lt_irrefl _) hb
    · have hkj : k.val < j.val := by omega
      let a : Fin N := ⟨k.val, by have hj := j.isLt; omega⟩
      have ha : a.castSucc = k := Fin.ext rfl
      have haj : a.succ ≤ j := by change k.val + 1 ≤ j.val; omega
      have hb := lt_of_lt_of_le (hr a ha) (f.monotone haj)
      rw [hj] at hb
      exact (lt_irrefl _) hb

/-- 各隣接辺が水平である頂点。総次数零では条件は空。 -/
def HorizontalVertex {m q : ℕ} (s : Cut m q) (k : Fin (m + q + 1)) : Prop :=
  (∀ a : Fin (m + q), a.succ = k → a ∈ s.val) ∧
  (∀ a : Fin (m + q), a.castSucc = k → a ∈ s.val)

/-- C56：一頂点だけの水平座標のfiberは、水平な両側の辺の条件と一致する。 -/
lemma horizontal_fiber_singleton_iff {m q : ℕ} (s : Cut m q) (k : Fin (m + q + 1)) :
    (∀ j, s.horizontal j = s.horizontal k → j = k) ↔ HorizontalVertex s k := by
  rw [monotone_fiber_singleton_iff]
  unfold HorizontalVertex
  constructor
  · rintro ⟨hl, hr⟩
    constructor
    · intro a ha
      apply (mem_iff_horizontal_lt s a).mpr
      rw [ha]
      exact hl a ha
    · intro a ha
      apply (mem_iff_horizontal_lt s a).mpr
      rw [ha]
      exact hr a ha
  · rintro ⟨hl, hr⟩
    constructor
    · intro a ha
      exact ha ▸ (mem_iff_horizontal_lt s a).mp (hl a ha)
    · intro a ha
      exact ha ▸ (mem_iff_horizontal_lt s a).mp (hr a ha)

end SerrePositivity.EInfinity.SimplexCuts
