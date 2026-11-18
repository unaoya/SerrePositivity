module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.BoundaryFaceTransfers

/-!
模型。文献の定義との比較は後で
# BFの全境界の有限な対合候補

Berger–Fresse §2.2.7、M14 L09a。
係数面と水平境界、入力面と垂直境界を既存の同値で交換し、混合角で角交換を使う。
ここでは添字の対合だけを証明し、符号付き境界値の相殺はまだ主張しない。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- C83：検証済みの挿入同値と角交換を全境界添字に貼り合わせた対応。 -/
def universalBoundaryPartner (m q : ℕ) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.UniversalBoundaryIndex m q →
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.UniversalBoundaryIndex m q
  | .inl t =>
    if hh : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryVertexKind t.1 t.2 = .horizontal then
      .inr (.inl ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.horizontalBoundaryAllEquiv m q (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.horizontal_kind_pos _ _ hh)).symm ⟨t, hh⟩))
    else if hv : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryVertexKind t.1 t.2 = .vertical then
      .inr (.inr ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.verticalBoundaryAllEquiv m q (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vertical_kind_pos _ _ hv)).symm ⟨t, hv⟩))
    else if _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryVertexKind t.1 t.2 = .mixed then .inl (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vertexCornerPerm m q t)
    else .inl t
  | .inr (.inl c) =>
    if hm : 0 < m then .inl ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.horizontalBoundaryAllEquiv m q hm) c).val else .inr (.inl c)
  | .inr (.inr v) =>
    if hq : 0 < q then .inl ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.verticalBoundaryAllEquiv m q hq) v).val else .inr (.inr v)

/-- C84：全境界添字の対応を二回適用すると同じ添字へ戻る。 -/
lemma universalBoundaryPartner_involutive (m q : ℕ) :
    Function.Involutive (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.universalBoundaryPartner m q) := by
  rintro (t | (c | v))
  · by_cases hh : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryVertexKind t.1 t.2 = .horizontal
    · have hm := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.horizontal_kind_pos t.1 t.2 hh
      simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.universalBoundaryPartner, dite_eq_left hh, dite_eq_left hm] using
        congrArg (fun x : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.BoundaryVertexOfKind m q .horizontal =>
          (Sum.inl x.val : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.UniversalBoundaryIndex m q))
          ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.horizontalBoundaryAllEquiv m q hm).apply_symm_apply ⟨t, hh⟩)
    · by_cases hv : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryVertexKind t.1 t.2 = .vertical
      · have hq := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vertical_kind_pos t.1 t.2 hv
        simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.universalBoundaryPartner, dite_eq_right hh, dite_eq_left hv,
          dite_eq_left hq] using
          congrArg (fun x : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.BoundaryVertexOfKind m q .vertical =>
            (Sum.inl x.val : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.UniversalBoundaryIndex m q))
            ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.verticalBoundaryAllEquiv m q hq).apply_symm_apply ⟨t, hv⟩)
      · by_cases hm : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryVertexKind t.1 t.2 = .mixed
        · have hm' : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryVertexKind (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vertexCornerPerm m q t).1
              (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vertexCornerPerm m q t).2 = .mixed := by
            rcases t with ⟨s, k⟩
            exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.mixed_kind_swapAtVertex s k hm
          have hh' : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryVertexKind (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vertexCornerPerm m q t).1
              (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vertexCornerPerm m q t).2 ≠ .horizontal := by rw [hm']; decide
          have hv' : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryVertexKind (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vertexCornerPerm m q t).1
              (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vertexCornerPerm m q t).2 ≠ .vertical := by rw [hm']; decide
          simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.universalBoundaryPartner, dite_eq_right hh, dite_eq_right hv,
            ite_eq_left hm, dite_eq_right hh', dite_eq_right hv', ite_eq_left hm'] using
            congrArg (fun x : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.MarkedCut m q => (Sum.inl x : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.UniversalBoundaryIndex m q))
              (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vertexCornerPerm_involutive m q t)
        · simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.universalBoundaryPartner, dite_eq_right hh, dite_eq_right hv,
            ite_eq_right hm]
  · by_cases hm : 0 < m
    · have hh := ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.horizontalBoundaryAllEquiv m q hm) c).property
      simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.universalBoundaryPartner, dite_eq_left hm, dite_eq_left hh] using
        congrArg (fun x : Fin (m + 1) × _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut (m - 1) q =>
          (Sum.inr (Sum.inl x) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.UniversalBoundaryIndex m q))
          ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.horizontalBoundaryAllEquiv m q hm).symm_apply_apply c)
    · simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.universalBoundaryPartner, dite_eq_right hm]
  · by_cases hq : 0 < q
    · have hv := ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.verticalBoundaryAllEquiv m q hq) v).property
      have hh : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryVertexKind ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.verticalBoundaryAllEquiv m q hq) v).val.1
          ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.verticalBoundaryAllEquiv m q hq) v).val.2 ≠ .horizontal := by rw [hv]; decide
      simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.universalBoundaryPartner, dite_eq_left hq, dite_eq_right hh,
        dite_eq_left hv] using
        congrArg (fun x : Fin (q + 1) × _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m (q - 1) =>
          (Sum.inr (Sum.inr x) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.UniversalBoundaryIndex m q))
          ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.verticalBoundaryAllEquiv m q hq).symm_apply_apply v)
    · simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.universalBoundaryPartner, dite_eq_right hq]

/-- C85：添字の対合候補を有限型の置換として保持する。 -/
def universalBoundaryPerm (m q : ℕ) : Equiv.Perm (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.UniversalBoundaryIndex m q) :=
  Function.Involutive.toPerm (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.universalBoundaryPartner m q)
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.universalBoundaryPartner_involutive m q)

/-- C86：元のBFの境界添字へ戻した、全境界の対合候補。 -/
def boundaryBalancePerm {r d : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (r + 1) d) (q : ℕ) :
    Equiv.Perm (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.BoundaryBalanceIndex u q) :=
  (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryBalanceIndexEquiv u q).trans
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.universalBoundaryPerm (r + d) q).trans (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryBalanceIndexEquiv u q).symm)

lemma boundaryBalancePerm_involutive {r d : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (r + 1) d)
    (q : ℕ) : Function.Involutive (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryBalancePerm u q) := by
  intro t
  apply (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryBalanceIndexEquiv u q).injective
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryBalancePerm, Equiv.trans_apply, Equiv.apply_symm_apply]
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.universalBoundaryPartner_involutive (r + d) q ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryBalanceIndexEquiv u q) t)

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
