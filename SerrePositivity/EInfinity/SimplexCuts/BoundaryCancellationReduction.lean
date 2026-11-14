module

public import SerrePositivity.EInfinity.SimplexCuts.BoundaryPartnerValues

/-!
# 三つの境界の相殺の貼り合わせ

Berger–Fresse §2.2.7、M14 L09aの証明分割。
水平・垂直・混合角の三群の符号付き値の等式から、全添字の等式を得る。
三群の等式自体をここで仮定なく証明したとは主張しない。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- L09aの証明分割：既存の対合の三群と固定点の零の等式を貼り合わせる。 -/
lemma universalBoundaryPartner_neg_of_cases {B : Type*} [AddCommGroup B] (m q : ℕ)
    (F : UniversalBoundaryIndex m q → B)
    (hfixed : ∀ i, universalBoundaryPartner m q i = i → F i = 0)
    (hc : ∀ (hm : 0 < m) (c : Fin (m + 1) × Cut (m - 1) q),
      F (.inl ((horizontalBoundaryAllEquiv m q hm) c).val) = -F (.inr (.inl c)))
    (hv : ∀ (hq : 0 < q) (v : Fin (q + 1) × Cut m (q - 1)),
      F (.inl ((verticalBoundaryAllEquiv m q hq) v).val) = -F (.inr (.inr v)))
    (hmix : ∀ t : BoundaryVertexOfKind m q .mixed,
      F (.inl (vertexCornerPerm m q t.val)) = -F (.inl t.val))
    (i : UniversalBoundaryIndex m q) :
    F (universalBoundaryPartner m q i) = -F i := by
  rcases i with t | (c | v)
  · by_cases hh : boundaryVertexKind t.1 t.2 = .horizontal
    · have hm := horizontal_kind_pos t.1 t.2 hh
      let c := (horizontalBoundaryAllEquiv m q hm).symm ⟨t, hh⟩
      have he : ((horizontalBoundaryAllEquiv m q hm) c).val = t :=
        congrArg Subtype.val ((horizontalBoundaryAllEquiv m q hm).apply_symm_apply ⟨t, hh⟩)
      have h := hc hm c
      rw [he] at h
      rw [universalBoundaryPartner_horizontal m q hm ⟨t, hh⟩]
      simpa only [neg_neg] using (congrArg Neg.neg h).symm
    · by_cases hv' : boundaryVertexKind t.1 t.2 = .vertical
      · have hq := vertical_kind_pos t.1 t.2 hv'
        let v := (verticalBoundaryAllEquiv m q hq).symm ⟨t, hv'⟩
        have he : ((verticalBoundaryAllEquiv m q hq) v).val = t :=
          congrArg Subtype.val ((verticalBoundaryAllEquiv m q hq).apply_symm_apply ⟨t, hv'⟩)
        have h := hv hq v
        rw [he] at h
        rw [universalBoundaryPartner_vertical m q hq ⟨t, hv'⟩]
        simpa only [neg_neg] using (congrArg Neg.neg h).symm
      · by_cases hm : boundaryVertexKind t.1 t.2 = .mixed
        · rw [universalBoundaryPartner_mixed m q ⟨t, hm⟩]
          exact hmix ⟨t, hm⟩
        · have hi : boundaryVertexKind t.1 t.2 = .isolated := by
            cases h : boundaryVertexKind t.1 t.2 <;> simp_all
          have hp := universalBoundaryPartner_isolated m q ⟨t, hi⟩
          have hz := hfixed (.inl t) hp
          rw [hp, hz]
          exact neg_zero.symm
  · by_cases hm : 0 < m
    · rw [universalBoundaryPartner_coefficient m q hm c]
      exact hc hm c
    · have hp : universalBoundaryPartner m q (.inr (.inl c)) = .inr (.inl c) := by
        simp only [universalBoundaryPartner, dite_eq_right hm]
      have hz := hfixed _ hp
      rw [hp, hz]
      exact neg_zero.symm
  · by_cases hq : 0 < q
    · rw [universalBoundaryPartner_input m q hq v]
      exact hv hq v
    · have hp : universalBoundaryPartner m q (.inr (.inr v)) = .inr (.inr v) := by
        simp only [universalBoundaryPartner, dite_eq_right hq]
      have hz := hfixed _ hp
      rw [hp, hz]
      exact neg_zero.symm

end SerrePositivity.EInfinity.SimplexCuts
