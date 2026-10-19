module
public import SerrePositivity.InfinityCategories.Derived.DGPretriangulatedQuasiEquivalence
public import SerrePositivity.InfinityCategories.Derived.DGQuotientPretriangulated
public import SerrePositivity.InfinityCategories.Derived.ResolvedDGQuotientNerve

/-! # 平坦分解後の dg 商の実安定性

概要：元の dg 圏が前三角なら、具体的 cell 分解を先行させた商の nerve は安定。
方針：増大の準同値で前三角性を反映し、証明済み局所 K-flat 条件を商へ渡す。
規約：元の Hom の K-flat 性を仮定しない。使われ方：β3 の導来 dg 商。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 具体的 cell 分解の源は元の dg 圏の前三角性を保つ。 -/
lemma dgCellResolutionSource_isDGPretriangulated [IsDGPretriangulated A D] :
    IsDGPretriangulated A (DGCategoryCellResolution.Source A D) :=
  isDGPretriangulated_of_quasiEquivalence A (DGCategoryCellResolution.Source A D) D
    (DGCategoryCellResolution.augmentation A D)
    (DGCategoryCellResolution.augmentation_quasiEquivalence A D)

/-- 元の Hom の平坦性を要求せず、平坦分解後の商は前三角。 -/
lemma resolvedDGQuotient_isDGPretriangulated [IsDGPretriangulated A D] (P : Set D) :
    IsDGPretriangulated A (DGQuotient.QuotientObject
      (DGCategoryCellResolution.Source A D) (resolvedDGNullObjects A D P)) := by
  let := dgCellResolutionSource_isDGPretriangulated A D
  exact dgQuotient_isDGPretriangulated A _ _ (resolvedDGQuotient_localKFlat A D P)

/-- 平坦分解後の実 dg 商の nerve は安定である。 -/
theorem resolvedDGQuotientNerve_isStable [IsDGPretriangulated A D] (P : Set D) :
    IsStable (resolvedDGQuotientNerve A D P) := by
  let := dgCellResolutionSource_isDGPretriangulated A D
  exact dgQuotientNerve_isStable A _ _ (resolvedDGQuotient_localKFlat A D P)

end SerrePositivity.InfinityCategories
