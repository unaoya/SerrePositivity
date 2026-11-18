module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.UniversalBoundaryPartner

/-!
模型。文献の定義との比較は後で
# 全境界の対合候補の固定点

Berger–Fresse §2.2.7、M14 L09a。
混合角は固定されず、水平・垂直の二群も交換されるため、零次数の余分な添字だけが残る。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- C87の証明分割：混合角の指定頂点付き経路は角交換で変わる。 -/
lemma mixed_vertexCornerPerm_ne {m q : ℕ} (t : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.MarkedCut m q)
    (ht : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryVertexKind t.1 t.2 = .mixed) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vertexCornerPerm m q t ≠ t := by
  rcases t with ⟨s, k⟩
  intro h
  have hs := congrArg Sigma.fst h
  exact ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.swapAtVertex_ne_iff s k).mpr ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryVertexKind_eq_mixed_iff s k).mp ht)) hs

/-- C87：全対合の固定点は、各群の零次数の余分な添字だけ。 -/
lemma universalBoundaryPartner_fixed_iff (m q : ℕ) (i : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.UniversalBoundaryIndex m q) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.universalBoundaryPartner m q i = i ↔
      match i with
      | .inl _ => m = 0 ∧ q = 0
      | .inr (.inl _) => m = 0
      | .inr (.inr _) => q = 0 := by
  rcases i with t | (c | v)
  · by_cases hh : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryVertexKind t.1 t.2 = .horizontal
    · have hp := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.horizontal_kind_pos t.1 t.2 hh
      simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.universalBoundaryPartner, dite_eq_left hh, Sum.inr_ne_inl, false_iff]
      omega
    · by_cases hv : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryVertexKind t.1 t.2 = .vertical
      · have hp := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vertical_kind_pos t.1 t.2 hv
        simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.universalBoundaryPartner, dite_eq_right hh, dite_eq_left hv,
          Sum.inr_ne_inl, false_iff]
        omega
      · by_cases hm : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryVertexKind t.1 t.2 = .mixed
        · have hn := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.mixed_vertexCornerPerm_ne t hm
          have hpos : 0 < m + q := by
            obtain ⟨h, _⟩ := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryVertexKind_eq_mixed_iff t.1 t.2).mp hm
            omega
          simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.universalBoundaryPartner, dite_eq_right hh, dite_eq_right hv,
            ite_eq_left hm, Sum.inl.injEq, hn, false_iff]
          omega
        · have hi : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryVertexKind t.1 t.2 = .isolated := by
            cases h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryVertexKind t.1 t.2 <;> simp_all
          have hz := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryVertexKind_eq_isolated_iff t.1 t.2).mp hi
          simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.universalBoundaryPartner, dite_eq_right hh, dite_eq_right hv,
            ite_eq_right hm, true_iff]
          exact hz
  · by_cases hm : 0 < m
    · simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.universalBoundaryPartner, dite_eq_left hm, Sum.inl_ne_inr, false_iff]
      omega
    · simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.universalBoundaryPartner, dite_eq_right hm, true_iff]
      omega
  · by_cases hq : 0 < q
    · simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.universalBoundaryPartner, dite_eq_left hq, Sum.inl_ne_inr, false_iff]
      omega
    · simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.universalBoundaryPartner, dite_eq_right hq, true_iff]
      omega

/-- C88：元の添字の固定点を、語に依らない同じ固定点の式へ移す。 -/
lemma boundaryBalancePerm_fixed_iff {r d : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (r + 1) d)
    (q : ℕ) (i : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.BoundaryBalanceIndex u q) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryBalancePerm u q i = i ↔
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.universalBoundaryPartner (r + d) q ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryBalanceIndexEquiv u q) i) =
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryBalanceIndexEquiv u q) i := by
  rw [← (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryBalanceIndexEquiv u q).injective.eq_iff]
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryBalancePerm, Equiv.trans_apply, Equiv.apply_symm_apply]
  rfl

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
