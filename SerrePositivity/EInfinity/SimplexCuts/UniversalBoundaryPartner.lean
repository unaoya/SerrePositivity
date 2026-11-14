module

public import SerrePositivity.EInfinity.SimplexCuts.BoundaryFaceTransfers

/-!
# BFの全境界の有限な対合候補

Berger–Fresse §2.2.7、M14 L09a。
係数面と水平境界、入力面と垂直境界を既存の同値で交換し、混合角で角交換を使う。
ここでは添字の対合だけを証明し、符号付き境界値の相殺はまだ主張しない。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- C83：検証済みの挿入同値と角交換を全境界添字に貼り合わせた対応。 -/
def universalBoundaryPartner (m q : ℕ) : UniversalBoundaryIndex m q →
    UniversalBoundaryIndex m q
  | .inl t =>
    if hh : boundaryVertexKind t.1 t.2 = .horizontal then
      .inr (.inl ((horizontalBoundaryAllEquiv m q (horizontal_kind_pos _ _ hh)).symm ⟨t, hh⟩))
    else if hv : boundaryVertexKind t.1 t.2 = .vertical then
      .inr (.inr ((verticalBoundaryAllEquiv m q (vertical_kind_pos _ _ hv)).symm ⟨t, hv⟩))
    else if boundaryVertexKind t.1 t.2 = .mixed then .inl (vertexCornerPerm m q t)
    else .inl t
  | .inr (.inl c) =>
    if hm : 0 < m then .inl ((horizontalBoundaryAllEquiv m q hm) c).val else .inr (.inl c)
  | .inr (.inr v) =>
    if hq : 0 < q then .inl ((verticalBoundaryAllEquiv m q hq) v).val else .inr (.inr v)

/-- C84：全境界添字の対応を二回適用すると同じ添字へ戻る。 -/
lemma universalBoundaryPartner_involutive (m q : ℕ) :
    Function.Involutive (universalBoundaryPartner m q) := by
  rintro (t | (c | v))
  · by_cases hh : boundaryVertexKind t.1 t.2 = .horizontal
    · have hm := horizontal_kind_pos t.1 t.2 hh
      simpa only [universalBoundaryPartner, dite_eq_left hh, dite_eq_left hm] using
        congrArg (fun x : BoundaryVertexOfKind m q .horizontal =>
          (Sum.inl x.val : UniversalBoundaryIndex m q))
          ((horizontalBoundaryAllEquiv m q hm).apply_symm_apply ⟨t, hh⟩)
    · by_cases hv : boundaryVertexKind t.1 t.2 = .vertical
      · have hq := vertical_kind_pos t.1 t.2 hv
        simpa only [universalBoundaryPartner, dite_eq_right hh, dite_eq_left hv,
          dite_eq_left hq] using
          congrArg (fun x : BoundaryVertexOfKind m q .vertical =>
            (Sum.inl x.val : UniversalBoundaryIndex m q))
            ((verticalBoundaryAllEquiv m q hq).apply_symm_apply ⟨t, hv⟩)
      · by_cases hm : boundaryVertexKind t.1 t.2 = .mixed
        · have hm' : boundaryVertexKind (vertexCornerPerm m q t).1
              (vertexCornerPerm m q t).2 = .mixed := by
            rcases t with ⟨s, k⟩
            exact mixed_kind_swapAtVertex s k hm
          have hh' : boundaryVertexKind (vertexCornerPerm m q t).1
              (vertexCornerPerm m q t).2 ≠ .horizontal := by rw [hm']; decide
          have hv' : boundaryVertexKind (vertexCornerPerm m q t).1
              (vertexCornerPerm m q t).2 ≠ .vertical := by rw [hm']; decide
          simpa only [universalBoundaryPartner, dite_eq_right hh, dite_eq_right hv,
            ite_eq_left hm, dite_eq_right hh', dite_eq_right hv', ite_eq_left hm'] using
            congrArg (fun x : MarkedCut m q => (Sum.inl x : UniversalBoundaryIndex m q))
              (vertexCornerPerm_involutive m q t)
        · simp only [universalBoundaryPartner, dite_eq_right hh, dite_eq_right hv,
            ite_eq_right hm]
  · by_cases hm : 0 < m
    · have hh := ((horizontalBoundaryAllEquiv m q hm) c).property
      simpa only [universalBoundaryPartner, dite_eq_left hm, dite_eq_left hh] using
        congrArg (fun x : Fin (m + 1) × Cut (m - 1) q =>
          (Sum.inr (Sum.inl x) : UniversalBoundaryIndex m q))
          ((horizontalBoundaryAllEquiv m q hm).symm_apply_apply c)
    · simp only [universalBoundaryPartner, dite_eq_right hm]
  · by_cases hq : 0 < q
    · have hv := ((verticalBoundaryAllEquiv m q hq) v).property
      have hh : boundaryVertexKind ((verticalBoundaryAllEquiv m q hq) v).val.1
          ((verticalBoundaryAllEquiv m q hq) v).val.2 ≠ .horizontal := by rw [hv]; decide
      simpa only [universalBoundaryPartner, dite_eq_left hq, dite_eq_right hh,
        dite_eq_left hv] using
        congrArg (fun x : Fin (q + 1) × Cut m (q - 1) =>
          (Sum.inr (Sum.inr x) : UniversalBoundaryIndex m q))
          ((verticalBoundaryAllEquiv m q hq).symm_apply_apply v)
    · simp only [universalBoundaryPartner, dite_eq_right hq]

/-- C85：添字の対合候補を有限型の置換として保持する。 -/
def universalBoundaryPerm (m q : ℕ) : Equiv.Perm (UniversalBoundaryIndex m q) :=
  Function.Involutive.toPerm (universalBoundaryPartner m q)
    (universalBoundaryPartner_involutive m q)

/-- C86：元のBFの境界添字へ戻した、全境界の対合候補。 -/
def boundaryBalancePerm {r d : ℕ} (u : Surjection.BasisWord (r + 1) d) (q : ℕ) :
    Equiv.Perm (BoundaryBalanceIndex u q) :=
  (boundaryBalanceIndexEquiv u q).trans
    ((universalBoundaryPerm (r + d) q).trans (boundaryBalanceIndexEquiv u q).symm)

lemma boundaryBalancePerm_involutive {r d : ℕ} (u : Surjection.BasisWord (r + 1) d)
    (q : ℕ) : Function.Involutive (boundaryBalancePerm u q) := by
  intro t
  apply (boundaryBalanceIndexEquiv u q).injective
  simp only [boundaryBalancePerm, Equiv.trans_apply, Equiv.apply_symm_apply]
  exact universalBoundaryPartner_involutive (r + d) q ((boundaryBalanceIndexEquiv u q) t)

end SerrePositivity.EInfinity.SimplexCuts
