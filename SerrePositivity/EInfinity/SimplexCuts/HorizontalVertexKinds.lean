module

public import SerrePositivity.EInfinity.SimplexCuts.BoundaryKindValues
public import SerrePositivity.EInfinity.SimplexCuts.SingletonFiberSteps

/-!
# 水平な境界頂点と水平な隣接辺

Berger–Fresse §2.2.7、M14 L09a。
端点も含む水平境界の判定を、隣接する辺への所属の条件と照合する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- C57：内部の水平頂点は二辺とも水平である条件。 -/
lemma horizontalVertex_interior_iff {m q : ℕ} (s : Cut m q) (k : Fin (m + q + 1))
    (h : 0 < k.val ∧ k.val < m + q) :
    HorizontalVertex s k ↔ cornerLeftEdge k h ∈ s.val ∧ cornerRightEdge k h ∈ s.val := by
  have hl : (cornerLeftEdge k h).succ = k := by
    apply Fin.ext
    change k.val - 1 + 1 = k.val
    omega
  have hr : (cornerRightEdge k h).castSucc = k := Fin.ext rfl
  constructor
  · intro hh
    exact ⟨hh.1 _ hl, hh.2 _ hr⟩
  · rintro ⟨ha, hb⟩
    constructor
    · intro a hk
      have he : a = cornerLeftEdge k h := by
        apply Fin.ext
        have hv := congrArg Fin.val hk
        change a.val + 1 = k.val at hv
        change a.val = k.val - 1
        omega
      exact he ▸ ha
    · intro a hk
      have he : a = cornerRightEdge k h := Fin.ext (congrArg (fun z : Fin (m + q + 1) => z.val) hk)
      exact he ▸ hb

/-- C58：始点では、最初の水平辺だけを要求する。 -/
lemma horizontalVertex_zero_iff {m q : ℕ} (s : Cut m q) (hN : 0 < m + q) :
    HorizontalVertex s 0 ↔ (⟨0, hN⟩ : Fin (m + q)) ∈ s.val := by
  constructor
  · intro h
    exact h.2 _ rfl
  · intro h
    constructor
    · intro a ha
      have hv := congrArg Fin.val ha
      simp only [Fin.val_succ, Fin.val_zero] at hv
      omega
    · intro a ha
      have he : a = ⟨0, hN⟩ := Fin.ext (congrArg (fun z : Fin (m + q + 1) => z.val) ha)
      exact he ▸ h

/-- C59：終点では、最後の水平辺だけを要求する。 -/
lemma horizontalVertex_last_iff {m q : ℕ} (s : Cut m q) (hN : 0 < m + q) :
    HorizontalVertex s (Fin.last (m + q)) ↔
      (⟨m + q - 1, by omega⟩ : Fin (m + q)) ∈ s.val := by
  constructor
  · intro h
    apply h.1
    apply Fin.ext
    change m + q - 1 + 1 = m + q
    omega
  · intro h
    constructor
    · intro a ha
      have he : a = (⟨m + q - 1, by omega⟩ : Fin (m + q)) := by
        apply Fin.ext
        have hv := congrArg Fin.val ha
        simp only [Fin.val_succ, Fin.val_last] at hv
        change a.val = m + q - 1
        omega
      exact he ▸ h
    · intro a ha
      have hv := congrArg Fin.val ha
      have hb := a.isLt
      simp only [Fin.val_castSucc, Fin.val_last] at hv
      omega

/-- C60：水平境界の種類は、正の総次数と水平な全隣接辺の条件。 -/
lemma boundaryVertexKind_eq_horizontal_iff {m q : ℕ} (s : Cut m q)
    (k : Fin (m + q + 1)) :
    boundaryVertexKind s k = .horizontal ↔ 0 < m + q ∧ HorizontalVertex s k := by
  by_cases hN : 0 < m + q
  · simp only [hN, true_and]
    by_cases h0 : k.val = 0
    · have hk : k = 0 := Fin.ext h0
      subst k
      rw [boundaryVertexKind_zero s hN, horizontalVertex_zero_iff s hN]
      split_ifs <;> simp_all
    · by_cases hlast : k.val = m + q
      · have hk : k = Fin.last (m + q) := Fin.ext hlast
        subst k
        rw [boundaryVertexKind_last s hN, horizontalVertex_last_iff s hN]
        split_ifs <;> simp_all
      · have h : 0 < k.val ∧ k.val < m + q := by have hk := k.isLt; omega
        rw [boundaryVertexKind_interior s k h, horizontalVertex_interior_iff s k h]
        split_ifs <;> simp_all
  · have hi : boundaryVertexKind s k = .isolated :=
      (boundaryVertexKind_eq_isolated_iff s k).mpr ⟨by omega, by omega⟩
    simp only [hi, hN, false_and, reduceCtorEq]

end SerrePositivity.EInfinity.SimplexCuts
