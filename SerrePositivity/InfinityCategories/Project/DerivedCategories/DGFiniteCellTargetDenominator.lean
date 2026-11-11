module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNativeDerivedDenominators
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators

/-! # 有限 cell 標的への導来射の元の閉分母による零化

概要：表現可能加群から指定有限 cell 標的への導来射を、元の実閉分母で消す。
方針：標的自身を有限因子分解に選び、既存分母を前三角性で元の閉射に戻す。
規約：商や K-flat 性を仮定しない。使われ方：最後辺の cone への残差の原始元。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded DGQuotient
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]

/-- 指定有限 cell 標的への任意の導来射は、元の実閉分母の前合成で零になる。 -/
theorem dgFiniteCellTarget_exists_closedDenominator (P : Set D) (x : D)
    {Y : DerivedModuleCategory A D} (hY : derivedFiniteCellOver A D P Y)
    (f : (moduleToDerived A D).obj
      (ForgetEnrichment.of (Complex A) (representable A x)) ⟶ Y) :
    ∃ (q : D) (s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A) x),
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D s).edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P ∧
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableDerivedMap A D s ≫ f = 0 := by
  have hx := (moduleFiniteCellOver A D Set.univ).prop_map_obj (moduleToDerived A D)
    (moduleFiniteCell_representable A D x)
  obtain ⟨E, hE, s, hs, hz⟩ := finiteCellFactor_exists_denominator A D P hx f
    ⟨Y, hY, f, 𝟙 Y, Category.comp_id f⟩
  obtain ⟨q, i, t, ht, htw⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgDerivedDenominator_exists_closed A D P x hE s hs
  refine ⟨q, t, (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge_mem_iff_derived_trW A D P t).mpr htw, ?_⟩
  rw [ht, Category.assoc, hz, Limits.comp_zero]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
