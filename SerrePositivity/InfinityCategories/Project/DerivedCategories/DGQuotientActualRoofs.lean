module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGQuotientClosedRoofs
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators

/-! # 有限 cell roof の native 実辺表示

概要：商の制限代表加群への主導来射を、元の dg nerve の実分母辺・実分子辺で表示する。
方針：閉 roof の二射を実辺へ送り、主導来分母と native 実分母の一致を使う。
規約：比較式はこの段階では主導来圏の等号。商の実二単体への昇格は別途必要。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded DGQuotient SSet
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]

/-- 元の dg 対象・実分母辺・実分子辺による roof と、その主導来比較式。 -/
structure DGQuotientActualRoof (P : Set D) (x z : D)
    (f : (_root_.SerrePositivity.DifferentialGraded.moduleToDerived A D).obj (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) (_root_.SerrePositivity.DifferentialGraded.representable A x)) ⟶
      (_root_.SerrePositivity.DifferentialGraded.moduleToDerived A D).obj
        (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) (_root_.SerrePositivity.DifferentialGraded.DGQuotient.quotientRepresentableRestriction A D P z))) where
  source : D
  denominator : Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex source) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)
  numerator : Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex source) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex z)
  denominator_mem : denominator.edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P
  comparison : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableDerivedMap A D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed numerator) ≫
    (_root_.SerrePositivity.DifferentialGraded.moduleToDerived A D).map
      (_root_.SerrePositivity.DifferentialGraded.representableRestrictionMap A D (_root_.SerrePositivity.DifferentialGraded.DGQuotient.QuotientObject D P) (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P) z) =
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableDerivedMap A D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed denominator) ≫ f

/-- 片側平坦条件を持つ商への任意の代表加群射は、元の native 実辺の roof を持つ。 -/
theorem dgQuotient_exists_actualRoof [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]
    (P : Set D) (hP : _root_.SerrePositivity.DifferentialGraded.DGQuotient.localKFlat A D P) (x z : D)
    (f : (_root_.SerrePositivity.DifferentialGraded.moduleToDerived A D).obj (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) (_root_.SerrePositivity.DifferentialGraded.representable A x)) ⟶
      (_root_.SerrePositivity.DifferentialGraded.moduleToDerived A D).obj
        (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) (_root_.SerrePositivity.DifferentialGraded.DGQuotient.quotientRepresentableRestriction A D P z))) :
    Nonempty (DGQuotientActualRoof A D P x z f) := by
  obtain ⟨q, s, g, hs, hg⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotient_exists_closedRoof A D P hP x z f
  refine ⟨{
    source := q
    denominator := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D s
    numerator := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D g
    denominator_mem := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge_mem_iff_derived_trW A D P s).mpr hs
    comparison := ?_ }⟩
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge_closed] using hg

end SerrePositivity.InfinityCategories.Project.DerivedCategories
