module
public import SerrePositivity.InfinityCategories.Derived.DGQuotientActualRelativeHomotopies
public import SerrePositivity.InfinityCategories.Derived.PinchedRelativeClosedRefinement

/-! # 指定有限境界の共通分母と実相対充填の保持データ

概要：共通実分母、全既知成分を保つ充填、指定商単体への実相対ホモトピーを保持する。
方針：有限相対充填の存在定理から、全ての証人を同時に回収する。
規約：指定した境界と目標を固定する。使われ方：実分母を追加する細分の反復。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGQuotient DGNerve DGNerve.PinchedHom SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [IsDGPretriangulated A D]

/-- 元の実分母と有限個の充填・実相対ホモトピーを、指定境界に対して保持する。 -/
structure DGQuotientRelativeFiller (P : Set D) {m n : ℕ} (x : D) (y : Fin m → D)
    (f : ∀ i, LinearData A x (y i) n)
    (g : ∀ i, LinearSimplex A ((inclusion A D P).obj x) ((inclusion A D P).obj (y i)) n) where
  source : D
  denominator : ForgetEnrichment.of (Complex A) source ⟶ ForgetEnrichment.of (Complex A) x
  denominator_mem : (dgClosedEdge A D denominator).edge ∈ dgVerdierEdges A D P
  simplex : ∀ i, LinearSimplex A source (y i) n
  proper : ∀ i J k (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)), J ≠ Finset.univ →
    (simplex i).val.component J k hJ hk =
      dgGradedPrecompose A D k ((f i).component J k hJ hk) denominator
  homotopy : ∀ i, PinchedRelativeHomotopy
    (pinchedLinearSimplexMap ((inclusion A D P).map source (y i)) (simplex i))
    (pinchedLinearSimplexMap (dgClosedPrecomposition A (QuotientObject D P)
      (q := (inclusion A D P).obj source) (x := (inclusion A D P).obj x)
      (y := (inclusion A D P).obj (y i)) ((inclusion A D P).onClosed.map denominator)) (g i))

/-- 有限相対充填の存在定理から、全証人を同時に保持するデータを得る。 -/
theorem dgQuotientRelativeFiller_nonempty (P : Set D) (hP : localKFlat A D P)
    {m n : ℕ} (x : D) (y : Fin m → D) (f : ∀ i, LinearData A x (y i) n)
    (he : ∀ i J k (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)), J ≠ Finset.univ →
      differential A ((f i).component J k hJ hk) = (f i).rhs J k hk)
    (g : ∀ i, LinearSimplex A ((inclusion A D P).obj x) ((inclusion A D P).obj (y i)) n)
    (hm : ∀ i J k (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)), J ≠ Finset.univ →
      ((inclusion A D P).map x (y i)).f k ((f i).component J k hJ hk) =
        (g i).val.component J k hJ hk) : Nonempty (DGQuotientRelativeFiller A D P x y f g) := by
  obtain ⟨q, s, hs, t, ht, hh⟩ :=
    dgQuotientFinite_exists_pinchedRelativeHomotopies A D P hP x y f he g hm
  exact ⟨⟨q, s, hs, t, ht, fun i => Classical.choice (hh i)⟩⟩

omit [IsDGPretriangulated A D] in
/-- 保持した全既知成分は、実際の全境界を指定分母後で厳密に充填する。 -/
lemma DGQuotientRelativeFiller.actual_boundary (P : Set D) {m n : ℕ} (x : D) (y : Fin m → D)
    (b : ∀ i, (∂Δ[n + 1] : SSet.{max u v}) ⟶ DGNerve.pinchedHom A D x (y i))
    (g : ∀ i, LinearSimplex A ((inclusion A D P).obj x) ((inclusion A D P).obj (y i)) (n + 1))
    (w : DGQuotientRelativeFiller A D P x y (fun i => pinchedBoundaryKnownData (b i)) g) (i) :
    (∂Δ[n + 1]).ι ≫ SSet.yonedaEquiv.symm (w.simplex i).toPinched =
      b i ≫ pinchedClosedPrecomposition A D w.denominator := by
  apply pinchedBoundary_eq_of_proper_components (dgClosedPrecomposition A D w.denominator)
  intro J k hJ hk hne
  exact (w.proper i J k hJ hk hne).trans (dgClosedPrecomposition_f A D w.denominator k
    ((pinchedBoundaryKnownData (b i)).component J k hJ hk)).symm

end SerrePositivity.InfinityCategories
