module

public import SerrePositivity.EInfinity.SimplexCuts.BoundaryFixedTerms

/-!
# 全境界の対合の各分岐での評価

Berger–Fresse §2.2.7、M14 L09aの証明分割。
検証済みの貼り合わせを、その三つの対応の同じ添字で評価する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

lemma universalBoundaryPartner_horizontal (m q : ℕ) (hm : 0 < m)
    (t : BoundaryVertexOfKind m q .horizontal) :
    universalBoundaryPartner m q (.inl t.val) =
      .inr (.inl ((horizontalBoundaryAllEquiv m q hm).symm t)) := by
  simp only [universalBoundaryPartner, dite_eq_left t.property]

lemma universalBoundaryPartner_vertical (m q : ℕ) (hq : 0 < q)
    (t : BoundaryVertexOfKind m q .vertical) :
    universalBoundaryPartner m q (.inl t.val) =
      .inr (.inr ((verticalBoundaryAllEquiv m q hq).symm t)) := by
  have hh : boundaryVertexKind t.val.1 t.val.2 ≠ .horizontal := by rw [t.property]; decide
  simp only [universalBoundaryPartner, dite_eq_right hh, dite_eq_left t.property]

lemma universalBoundaryPartner_mixed (m q : ℕ) (t : BoundaryVertexOfKind m q .mixed) :
    universalBoundaryPartner m q (.inl t.val) = .inl (vertexCornerPerm m q t.val) := by
  have hh : boundaryVertexKind t.val.1 t.val.2 ≠ .horizontal := by rw [t.property]; decide
  have hv : boundaryVertexKind t.val.1 t.val.2 ≠ .vertical := by rw [t.property]; decide
  simp only [universalBoundaryPartner, dite_eq_right hh, dite_eq_right hv, ite_eq_left t.property]

lemma universalBoundaryPartner_coefficient (m q : ℕ) (hm : 0 < m)
    (c : Fin (m + 1) × Cut (m - 1) q) :
    universalBoundaryPartner m q (.inr (.inl c)) =
      .inl ((horizontalBoundaryAllEquiv m q hm) c).val := by
  simp only [universalBoundaryPartner, dite_eq_left hm]

lemma universalBoundaryPartner_input (m q : ℕ) (hq : 0 < q)
    (v : Fin (q + 1) × Cut m (q - 1)) :
    universalBoundaryPartner m q (.inr (.inr v)) =
      .inl ((verticalBoundaryAllEquiv m q hq) v).val := by
  simp only [universalBoundaryPartner, dite_eq_left hq]

lemma universalBoundaryPartner_isolated (m q : ℕ)
    (t : BoundaryVertexOfKind m q .isolated) :
    universalBoundaryPartner m q (.inl t.val) = .inl t.val := by
  have hh : boundaryVertexKind t.val.1 t.val.2 ≠ .horizontal := by rw [t.property]; decide
  have hv : boundaryVertexKind t.val.1 t.val.2 ≠ .vertical := by rw [t.property]; decide
  have hm : boundaryVertexKind t.val.1 t.val.2 ≠ .mixed := by rw [t.property]; decide
  simp only [universalBoundaryPartner, dite_eq_right hh, dite_eq_right hv, ite_eq_right hm]

end SerrePositivity.EInfinity.SimplexCuts
