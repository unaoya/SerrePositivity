module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGQuotientClosedRoofs

/-! # 比較写像の核の元の閉 dg 分母による零化

概要：制限代表への比較後に零になる主導来射は、元の閉 dg 分母で前合成すると既に零。
方針：有限 cell 分母の存在から始域を表現可能へ戻し、分母を閉射として回収する。
規約：局所 K-flat 条件を公開する。使われ方：商で一致する二射の相対均等化。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded DGQuotient
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]

/-- 比較後に零になる導来射は、元の対象からの閉 dg 分母の前合成で零になる。 -/
theorem dgQuotientKernel_exists_closedDenominator (P : Set D) (hP : localKFlat A D P)
    (x y : D)
    (f : (moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) (representable A x)) ⟶
      (moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) (representable A y)))
    (hf : f ≫ (moduleToDerived A D).map
      (representableRestrictionMap A D (QuotientObject D P) (inclusion A D P) y) = 0) :
    ∃ (q : D) (s : (ForgetEnrichment.of (Complex A) q) ⟶
      (ForgetEnrichment.of (Complex A) x)),
      (derivedFiniteCellOver A D P).trW (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableDerivedMap A D s) ∧
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableDerivedMap A D s ≫ f = 0 := by
  have hx := (moduleFiniteCellOver A D Set.univ).prop_map_obj (moduleToDerived A D)
    (moduleFiniteCell_representable A D x)
  obtain ⟨E, hE, s, hs, hz⟩ := comparison_zero_exists_finiteCell_denominator A D P
    (moduleDerivedConeTriangle A D
      (representableRestrictionMap A D (QuotientObject D P) (inclusion A D P) y))
    (moduleDerivedConeTriangle_distinguished A D _)
    (quotientRepresentableComparisonCone_finiteCellFactorTarget A D P hP y) hx f hf
  obtain ⟨q, ⟨e⟩⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTria_isRepresentable A D (⟨E, hE⟩ : TriaCategory A D)
  let i := (triaInclusion A D).mapIso e
  obtain ⟨s', hs'⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableDerivedMap_surjective A D
    (ForgetEnrichment.of (Complex A) q) (ForgetEnrichment.of (Complex A) x) (i.inv ≫ s)
  refine ⟨q, s', ?_, ?_⟩
  · rw [hs']
    exact ((derivedFiniteCellOver A D P).trW.arrow_mk_iso_iff
      (Arrow.isoMk i (Iso.refl _) (by simp))).mp hs
  · rw [hs', Category.assoc, hz, Limits.comp_zero]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
