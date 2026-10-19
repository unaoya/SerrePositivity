module
public import SerrePositivity.InfinityCategories.Derived.DGQuotientPinchedTopComparisons
public import SerrePositivity.InfinityCategories.Derived.PinchedRelativeHomotopy

/-! # 有限共通実分母の後の指定商単体への実相対ホモトピー

概要：全指定面を保つ元の充填と指定商単体の前合成を、全境界上定値の実ホモトピーで比較。
方針：最上位比較の指定原始元から全次元の錐 prism を構成する定理を適用する。
規約：零次元を含む有限族を同時に扱う。使われ方：β3 の相対写像空間の局所化比較。
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

/-- 全境界を保つ有限族の充填は、指定商単体の前合成と実相対ホモトピーで比較できる。 -/
theorem dgQuotientFinite_exists_pinchedRelativeHomotopies (P : Set D) (hP : localKFlat A D P)
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
        ∀ i, Nonempty (PinchedRelativeHomotopy
          (pinchedLinearSimplexMap ((inclusion A D P).map q (y i)) (t i))
          (pinchedLinearSimplexMap
            (dgClosedPrecomposition A (QuotientObject D P)
              (q := (inclusion A D P).obj q) (x := (inclusion A D P).obj x)
              (y := (inclusion A D P).obj (y i)) ((inclusion A D P).onClosed.map s))
              (g i))) := by
  obtain ⟨q, s, hs, t, ht, hc⟩ :=
    dgQuotientFinite_exists_pinchedTopComparisons A D P hP x y f he g hm
  refine ⟨q, s, hs, t, ht, ?_⟩
  intro i
  obtain ⟨c⟩ := hc i
  exact ⟨c.relativeHomotopy⟩

end SerrePositivity.InfinityCategories
