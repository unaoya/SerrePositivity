module
public import SerrePositivity.InfinityCategories.Derived.DGQuotientShiftedKernel
public import SerrePositivity.InfinityCategories.Derived.DGDerivedEdgeComposition
public import SerrePositivity.InfinityCategories.Derived.DGFiniteVerdierDenominators

/-! # 異なる次数の有限個の商比較の核の同時零化

概要：任意の有限個のシフト次数の比較の核を、一つの元の実分母で同時に零化する。
方針：各次数の分母を実共通分母で細分し、実二単体の導来合成式を使う。
規約：全次数に一つの分母を使う。使われ方：有限高次境界の障害の相対零化。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGQuotient DGNerve DGNerve.HomotopyComparison SSet
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [IsDGPretriangulated A D]

/-- 有限個の異なる次数の核を、一つの元の実 Verdier 分母で同時に零化する。 -/
theorem dgQuotientFiniteShiftedKernel_exists_denominator (P : Set D)
    (hP : localKFlat A D P) {m : ℕ} (x : D) (y : Fin m → D) (n : Fin m → ℤ)
    (f : ∀ i, (moduleToDerived A D).obj
      (ForgetEnrichment.of (Complex A) (representable A x)) ⟶
        ((moduleToDerived A D).obj
          (ForgetEnrichment.of (Complex A) (representable A (y i))))⟦n i⟧)
    (hf : ∀ i, f i ≫ ((moduleToDerived A D).map
      (representableRestrictionMap A D (QuotientObject D P) (inclusion A D P) (y i)))⟦n i⟧'
        = 0) :
    ∃ (q : D) (s : Truncated.Edge (X := (truncation 2).obj (dgNerve A D))
      (Simplex.vertex q) (Simplex.vertex x)), s.edge ∈ dgVerdierEdges A D P ∧
        ∀ i, dgRepresentableDerivedEdgeMap A D s ≫ f i = 0 := by
  choose q s hs hz using fun i =>
    dgQuotientShiftedKernel_exists_closedDenominator A D P hP x (y i) (n i) (f i) (hf i)
  obtain ⟨q', t, ht, r, hr⟩ := dgVerdierEdges_commonDenominator A D P q
    (fun i => dgClosedEdge A D (s i)) hs
  refine ⟨q', t, ht, fun i => ?_⟩
  rw [← dgRepresentableDerivedEdgeMap_compStruct A D (hr i).2.some, Category.assoc]
  change dgRepresentableDerivedEdgeMap A D (r i) ≫
    dgRepresentableDerivedMap A D (edgeClosed (dgClosedEdge A D (s i))) ≫ f i = 0
  rw [dgClosedEdge_closed, hz i, Limits.comp_zero]

end SerrePositivity.InfinityCategories
