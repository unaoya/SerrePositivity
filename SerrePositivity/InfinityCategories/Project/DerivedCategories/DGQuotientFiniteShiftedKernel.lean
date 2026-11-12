module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGQuotientShiftedKernel
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGDerivedEdgeComposition
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFiniteVerdierDenominators

/-! # 異なる次数の有限個の商比較の核の同時零化

概要：任意の有限個のシフト次数の比較の核を、一つの元の実分母で同時に零化する。
方針：各次数の分母を実共通分母で細分し、実二単体の導来合成式を使う。
規約：全次数に一つの分母を使う。使われ方：有限高次境界の障害の相対零化。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded DGQuotient SSet
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]

/-- 有限個の異なる次数の核を、一つの元の実 Verdier 分母で同時に零化する。 -/
theorem dgQuotientFiniteShiftedKernel_exists_denominator (P : Set D)
    (hP : _root_.SerrePositivity.DifferentialGraded.DGQuotient.localKFlat A D P) {m : ℕ} (x : D) (y : Fin m → D) (n : Fin m → ℤ)
    (f : ∀ i, (_root_.SerrePositivity.DifferentialGraded.moduleToDerived A D).obj
      (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) (_root_.SerrePositivity.DifferentialGraded.representable A x)) ⟶
        ((_root_.SerrePositivity.DifferentialGraded.moduleToDerived A D).obj
          (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) (_root_.SerrePositivity.DifferentialGraded.representable A (y i))))⟦n i⟧)
    (hf : ∀ i, f i ≫ ((_root_.SerrePositivity.DifferentialGraded.moduleToDerived A D).map
      (_root_.SerrePositivity.DifferentialGraded.representableRestrictionMap A D (_root_.SerrePositivity.DifferentialGraded.DGQuotient.QuotientObject D P) (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P) (y i)))⟦n i⟧'
        = 0) :
    ∃ (q : D) (s : Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex q) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)), s.edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P ∧
        ∀ i, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableDerivedEdgeMap A D s ≫ f i = 0 := by
  choose q s hs hz using fun i =>
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientShiftedKernel_exists_closedDenominator A D P hP x (y i) (n i) (f i) (hf i)
  obtain ⟨q', t, ht, r, hr⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges_commonDenominator A D P q
    (fun i => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D (s i)) hs
  refine ⟨q', t, ht, fun i => ?_⟩
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableDerivedEdgeMap_compStruct A D (hr i).2.some, Category.assoc]
  change _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableDerivedEdgeMap A D (r i) ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableDerivedMap A D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D (s i))) ≫ f i = 0
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge_closed, hz i, Limits.comp_zero]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
