module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNativeDerivedDenominators
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators

/-! # 全整数シフトでの商比較の核の元の実分母による零化

概要：任意次数のシフトされた比較で零になる導来射を、元の実分母で零化する。
方針：比較三角形と有限因子分解性を同じ整数でシフトし、始域だけを元へ戻す。
規約：シフトは任意の整数。使われ方：高次 Hom の境界の有限個の障害の零化。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded DGQuotient Pretriangulated
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]

/-- シフトされた比較の核は、元の実 Verdier 分母の前合成で零化できる。 -/
theorem dgQuotientShiftedKernel_exists_closedDenominator (P : Set D)
    (hP : localKFlat A D P) (x y : D) (n : ℤ)
    (f : (moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) (representable A x)) ⟶
      ((moduleToDerived A D).obj
        (ForgetEnrichment.of (Complex A) (representable A y)))⟦n⟧)
    (hf : f ≫ ((moduleToDerived A D).map
      (representableRestrictionMap A D (QuotientObject D P) (inclusion A D P) y))⟦n⟧' = 0) :
    ∃ (q : D) (s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A) x),
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D s).edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P ∧
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableDerivedMap A D s ≫ f = 0 := by
  let T := moduleDerivedConeTriangle A D
    (representableRestrictionMap A D (QuotientObject D P) (inclusion A D P) y)
  have hT := moduleDerivedConeTriangle_distinguished A D
    (representableRestrictionMap A D (QuotientObject D P) (inclusion A D P) y)
  have hC := moduleFiniteCellFactorTarget_shift A D
    (quotientRepresentableComparisonCone_finiteCellFactorTarget A D P hP y) n
  have hx := (moduleFiniteCellOver A D Set.univ).prop_map_obj (moduleToDerived A D)
    (moduleFiniteCell_representable A D x)
  obtain ⟨E, hE, s, hs, hz⟩ := comparison_zero_exists_finiteCell_denominator A D P
    (T⟦n⟧) (Triangle.shift_distinguished T hT n) hC hx f (by
      change f ≫ (n.negOnePow • ((moduleToDerived A D).map
        (representableRestrictionMap A D (QuotientObject D P) (inclusion A D P) y))⟦n⟧') = 0
      rw [Linear.comp_units_smul, hf, smul_zero])
  obtain ⟨q, i, t, ht, htw⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgDerivedDenominator_exists_closed A D P x hE s hs
  refine ⟨q, t, (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge_mem_iff_derived_trW A D P t).mpr htw, ?_⟩
  rw [ht, Category.assoc, hz, Limits.comp_zero]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
