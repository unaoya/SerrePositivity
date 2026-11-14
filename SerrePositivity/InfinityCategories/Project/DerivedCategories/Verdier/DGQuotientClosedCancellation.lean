module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGQuotientRestrictionEquality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGQuotientKernelDenominators

/-! # 商で一致する二閉射の実分母による相対均等化

概要：商の H⁰ で一致する元の二閉射は、元の実 Verdier 分母で前合成すると H⁰ で一致。
方針：代表加群比較後の差を零化し、導来等号を元の H⁰ へ反映する。
規約：局所 K-flat 条件を公開する。使われ方：共有合成辺を持つ実二単体の回収。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded DGQuotient
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]

/-- 商で一致する二閉射は、元の実分母の前合成によって既に H⁰ で一致する。 -/
theorem dgQuotientClosed_exists_cancelingDenominator (P : Set D) (hP : localKFlat A D P)
    {x y : ClosedCategory A D} (f g : x ⟶ y)
    (h : (toHomotopy A (QuotientObject D P)).map ((inclusion A D P).onClosed.map f) =
      (toHomotopy A (QuotientObject D P)).map ((inclusion A D P).onClosed.map g)) :
    ∃ (q : D) (s : (ForgetEnrichment.of (Complex A) q) ⟶ x),
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D s).edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P ∧
      (toHomotopy A D).map (s ≫ f) = (toHomotopy A D).map (s ≫ g) := by
  have he := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientClosed_eq_iff_restriction A D P f g).mp h
  have hz : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableDerivedMap A D f - _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableDerivedMap A D g) ≫
      (moduleToDerived A D).map (representableRestrictionMap A D
        (QuotientObject D P) (inclusion A D P) y) = 0 := by
    rw [Preadditive.sub_comp, he, sub_self]
  obtain ⟨q, s, hs, hzero⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientKernel_exists_closedDenominator A D P hP x y _ hz
  have hc : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableDerivedMap A D s ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableDerivedMap A D f =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableDerivedMap A D s ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableDerivedMap A D g :=
    sub_eq_zero.mp (by rw [← Preadditive.comp_sub]; exact hzero)
  refine ⟨q, s, (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge_mem_iff_derived_trW A D P s).mpr hs, ?_⟩
  apply (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableDerivedMap_eq_iff A D (s ≫ f) (s ≫ g)).mp
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableDerivedMap, Functor.map_comp] using hc

end SerrePositivity.InfinityCategories.Project.DerivedCategories
