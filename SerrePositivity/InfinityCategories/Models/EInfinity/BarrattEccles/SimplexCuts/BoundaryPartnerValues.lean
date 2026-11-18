module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.BoundaryFixedTerms

/-!
模型。文献の定義との比較は後で
# 全境界の対合の各分岐での評価

Berger–Fresse §2.2.7、M14 L09aの証明分割。
検証済みの貼り合わせを、その三つの対応の同じ添字で評価する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

lemma universalBoundaryPartner_horizontal (m q : ℕ) (hm : 0 < m)
    (t : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.BoundaryVertexOfKind m q .horizontal) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.universalBoundaryPartner m q (.inl t.val) =
      .inr (.inl ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.horizontalBoundaryAllEquiv m q hm).symm t)) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.universalBoundaryPartner, dite_eq_left t.property]

lemma universalBoundaryPartner_vertical (m q : ℕ) (hq : 0 < q)
    (t : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.BoundaryVertexOfKind m q .vertical) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.universalBoundaryPartner m q (.inl t.val) =
      .inr (.inr ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.verticalBoundaryAllEquiv m q hq).symm t)) := by
  have hh : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryVertexKind t.val.1 t.val.2 ≠ .horizontal := by rw [t.property]; decide
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.universalBoundaryPartner, dite_eq_right hh, dite_eq_left t.property]

lemma universalBoundaryPartner_mixed (m q : ℕ) (t : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.BoundaryVertexOfKind m q .mixed) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.universalBoundaryPartner m q (.inl t.val) = .inl (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vertexCornerPerm m q t.val) := by
  have hh : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryVertexKind t.val.1 t.val.2 ≠ .horizontal := by rw [t.property]; decide
  have hv : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryVertexKind t.val.1 t.val.2 ≠ .vertical := by rw [t.property]; decide
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.universalBoundaryPartner, dite_eq_right hh, dite_eq_right hv, ite_eq_left t.property]

lemma universalBoundaryPartner_coefficient (m q : ℕ) (hm : 0 < m)
    (c : Fin (m + 1) × _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut (m - 1) q) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.universalBoundaryPartner m q (.inr (.inl c)) =
      .inl ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.horizontalBoundaryAllEquiv m q hm) c).val := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.universalBoundaryPartner, dite_eq_left hm]

lemma universalBoundaryPartner_input (m q : ℕ) (hq : 0 < q)
    (v : Fin (q + 1) × _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m (q - 1)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.universalBoundaryPartner m q (.inr (.inr v)) =
      .inl ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.verticalBoundaryAllEquiv m q hq) v).val := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.universalBoundaryPartner, dite_eq_left hq]

lemma universalBoundaryPartner_isolated (m q : ℕ)
    (t : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.BoundaryVertexOfKind m q .isolated) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.universalBoundaryPartner m q (.inl t.val) = .inl t.val := by
  have hh : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryVertexKind t.val.1 t.val.2 ≠ .horizontal := by rw [t.property]; decide
  have hv : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryVertexKind t.val.1 t.val.2 ≠ .vertical := by rw [t.property]; decide
  have hm : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryVertexKind t.val.1 t.val.2 ≠ .mixed := by rw [t.property]; decide
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.universalBoundaryPartner, dite_eq_right hh, dite_eq_right hv, ite_eq_right hm]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
