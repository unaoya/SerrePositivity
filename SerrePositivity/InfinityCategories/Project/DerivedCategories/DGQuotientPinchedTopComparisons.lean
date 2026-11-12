module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedTopComparison

/-! # 有限共通分母の後の実商像と指定線形単体の最上位比較

概要：元の充填の商像と、指定商単体の前合成の間に最上位比較を構成する。
方針：共通分母の充填の既知成分を関手自然性へ渡し、残差の原始元を再利用する。
規約：全次元と有限族を同じ構成で扱う。使われ方：実相対ホモトピーへの昇格。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded DGQuotient
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]

/-- 全境界を保つ有限族の充填は、指定商単体の前合成と最上位比較を持つ。 -/
theorem dgQuotientFinite_exists_pinchedTopComparisons (P : Set D) (hP : _root_.SerrePositivity.DifferentialGraded.DGQuotient.localKFlat A D P)
    {m n : ℕ} (x : D) (y : Fin m → D) (f : ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData A x (y i) n)
    (he : ∀ i J k (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)), J ≠ Finset.univ →
      _root_.SerrePositivity.DifferentialGraded.differential A ((f i).component J k hJ hk) = (f i).rhs J k hk)
    (g : ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A ((inclusion A D P).obj x) ((inclusion A D P).obj (y i)) n)
    (hm : ∀ i J k (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)), J ≠ Finset.univ →
      ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).map x (y i)).f k ((f i).component J k hJ hk) =
        (g i).val.component J k hJ hk) :
    ∃ (q : D) (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x),
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D s).edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P ∧
      ∃ t : ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A q (y i) n,
        (∀ i J k (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)), J ≠ Finset.univ →
          (t i).val.component J k hJ hk =
            _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose A D k ((f i).component J k hJ hk) s) ∧
        ∀ i, Nonempty (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedTopComparison
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearSimplexMap ((inclusion A D P).map q (y i)) (t i))
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearSimplexMap
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecomposition A (QuotientObject D P)
              (q := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj q) (x := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj x)
              (y := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj (y i)) ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).onClosed.map s))
              (g i))) := by
  obtain ⟨q, s, hs, t, ht, hb⟩ :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientFinite_exists_pinchedBoundaryFillers A D P hP x y f he g hm
  refine ⟨q, s, hs, t, ht, ?_⟩
  intro i
  obtain ⟨e, he⟩ := hb i
  refine ⟨⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedMappedBoundaryComparison_proper (inclusion A D P) s (f i) (g i) (t i)
    (ht i) (hm i), e, ?_⟩⟩
  change _ = ((inclusion A D P).map q (y i)).f (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedTopDegree n)
    ((t i).val.component Finset.univ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedTopDegree n) Finset.univ_nonempty rfl) -
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecomposition A (QuotientObject D P)
              (q := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj q) (x := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj x)
              (y := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj (y i)) ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).onClosed.map s)).f
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedTopDegree n)
      ((g i).val.component Finset.univ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedTopDegree n) Finset.univ_nonempty rfl)
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecomposition_f]
  exact he

end SerrePositivity.InfinityCategories.Project.DerivedCategories
