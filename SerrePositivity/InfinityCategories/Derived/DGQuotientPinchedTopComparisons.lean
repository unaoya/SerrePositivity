module
public import SerrePositivity.InfinityCategories.Derived.PinchedTopComparison

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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGQuotient DGNerve DGNerve.PinchedHom
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [IsDGPretriangulated A D]

/-- 全境界を保つ有限族の充填は、指定商単体の前合成と最上位比較を持つ。 -/
theorem dgQuotientFinite_exists_pinchedTopComparisons (P : Set D) (hP : localKFlat A D P)
    {m n : ℕ} (x : D) (y : Fin m → D) (f : ∀ i, LinearData A x (y i) n)
    (he : ∀ i J k (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)), J ≠ Finset.univ →
      differential A ((f i).component J k hJ hk) = (f i).rhs J k hk)
    (g : ∀ i, LinearSimplex A ((inclusion A D P).obj x) ((inclusion A D P).obj (y i)) n)
    (hm : ∀ i J k (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)), J ≠ Finset.univ →
      ((inclusion A D P).map x (y i)).f k ((f i).component J k hJ hk) =
        (g i).val.component J k hJ hk) :
    ∃ (q : D) (s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A) x),
      (dgClosedEdge A D s).edge ∈ dgVerdierEdges A D P ∧
      ∃ t : ∀ i, LinearSimplex A q (y i) n,
        (∀ i J k (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)), J ≠ Finset.univ →
          (t i).val.component J k hJ hk =
            dgGradedPrecompose A D k ((f i).component J k hJ hk) s) ∧
        ∀ i, Nonempty (PinchedTopComparison
          (pinchedLinearSimplexMap ((inclusion A D P).map q (y i)) (t i))
          (pinchedLinearSimplexMap
            (dgClosedPrecomposition A (QuotientObject D P)
              (q := (inclusion A D P).obj q) (x := (inclusion A D P).obj x)
              (y := (inclusion A D P).obj (y i)) ((inclusion A D P).onClosed.map s))
              (g i))) := by
  obtain ⟨q, s, hs, t, ht, hb⟩ :=
    dgQuotientFinite_exists_pinchedBoundaryFillers A D P hP x y f he g hm
  refine ⟨q, s, hs, t, ht, ?_⟩
  intro i
  obtain ⟨e, he⟩ := hb i
  refine ⟨⟨pinchedMappedBoundaryComparison_proper (inclusion A D P) s (f i) (g i) (t i)
    (ht i) (hm i), e, ?_⟩⟩
  change _ = ((inclusion A D P).map q (y i)).f (pinchedTopDegree n)
    ((t i).val.component Finset.univ (pinchedTopDegree n) Finset.univ_nonempty rfl) -
    (dgClosedPrecomposition A (QuotientObject D P)
              (q := (inclusion A D P).obj q) (x := (inclusion A D P).obj x)
              (y := (inclusion A D P).obj (y i)) ((inclusion A D P).onClosed.map s)).f
      (pinchedTopDegree n)
      ((g i).val.component Finset.univ (pinchedTopDegree n) Finset.univ_nonempty rfl)
  rw [dgClosedPrecomposition_f]
  exact he

end SerrePositivity.InfinityCategories
