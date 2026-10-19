module
public import SerrePositivity.InfinityCategories.Derived.DGQuotientClosedRoofs
public import SerrePositivity.InfinityCategories.Derived.DGClosedVerdierDenominators

/-! # 有限 cell roof の native 実辺表示

概要：商の制限代表加群への主導来射を、元の dg nerve の実分母辺・実分子辺で表示する。
方針：閉 roof の二射を実辺へ送り、主導来分母と native 実分母の一致を使う。
規約：比較式はこの段階では主導来圏の等号。商の実二単体への昇格は別途必要。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGQuotient DGNerve DGNerve.HomotopyComparison SSet
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 元の dg 対象・実分母辺・実分子辺による roof と、その主導来比較式。 -/
structure DGQuotientActualRoof (P : Set D) (x z : D)
    (f : (moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) (representable A x)) ⟶
      (moduleToDerived A D).obj
        (ForgetEnrichment.of (Complex A) (quotientRepresentableRestriction A D P z))) where
  source : D
  denominator : Truncated.Edge (X := (truncation 2).obj (dgNerve A D))
    (Simplex.vertex source) (Simplex.vertex x)
  numerator : Truncated.Edge (X := (truncation 2).obj (dgNerve A D))
    (Simplex.vertex source) (Simplex.vertex z)
  denominator_mem : denominator.edge ∈ dgVerdierEdges A D P
  comparison : dgRepresentableDerivedMap A D (edgeClosed numerator) ≫
    (moduleToDerived A D).map
      (representableRestrictionMap A D (QuotientObject D P) (inclusion A D P) z) =
        dgRepresentableDerivedMap A D (edgeClosed denominator) ≫ f

/-- 片側平坦条件を持つ商への任意の代表加群射は、元の native 実辺の roof を持つ。 -/
theorem dgQuotient_exists_actualRoof [IsDGPretriangulated A D]
    (P : Set D) (hP : localKFlat A D P) (x z : D)
    (f : (moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) (representable A x)) ⟶
      (moduleToDerived A D).obj
        (ForgetEnrichment.of (Complex A) (quotientRepresentableRestriction A D P z))) :
    Nonempty (DGQuotientActualRoof A D P x z f) := by
  obtain ⟨q, s, g, hs, hg⟩ := dgQuotient_exists_closedRoof A D P hP x z f
  refine ⟨{
    source := q
    denominator := dgClosedEdge A D s
    numerator := dgClosedEdge A D g
    denominator_mem := (dgClosedEdge_mem_iff_derived_trW A D P s).mpr hs
    comparison := ?_ }⟩
  simpa only [dgClosedEdge_closed] using hg

end SerrePositivity.InfinityCategories
