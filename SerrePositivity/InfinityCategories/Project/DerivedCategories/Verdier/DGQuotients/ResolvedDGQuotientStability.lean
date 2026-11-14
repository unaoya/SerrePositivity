module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Triangles.DGPretriangulatedQuasiEquivalence
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGQuotientPretriangulated
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.ResolvedDGQuotientNerve

/-! # 平坦分解後の dg 商の実安定性

概要：元の dg 圏が前三角なら、具体的 cell 分解を先行させた商の nerve は安定。
方針：増大の準同値で前三角性を反映し、証明済み局所 K-flat 条件を商へ渡す。
規約：元の Hom の K-flat 性を仮定しない。使われ方：β3 の導来 dg 商。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 具体的 cell 分解の源は元の dg 圏の前三角性を保つ。 -/
lemma dgCellResolutionSource_isDGPretriangulated [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D] :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A (DGCategoryCellResolution.Source A D) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.isDGPretriangulated_of_quasiEquivalence A (DGCategoryCellResolution.Source A D) D
    (DGCategoryCellResolution.augmentation A D)
    (DGCategoryCellResolution.augmentation_quasiEquivalence A D)

/-- 元の Hom の平坦性を要求せず、平坦分解後の商は前三角。 -/
lemma resolvedDGQuotient_isDGPretriangulated [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D] (P : Set D) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A (DGQuotient.QuotientObject
      (DGCategoryCellResolution.Source A D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGNullObjects A D P)) := by
  let := dgCellResolutionSource_isDGPretriangulated A D
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotient_isDGPretriangulated A _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotient_localKFlat A D P)

/-- 平坦分解後の実 dg 商の nerve は安定である。 -/
theorem resolvedDGQuotientNerve_isStable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D] (P : Set D) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientNerve A D P) := by
  let := dgCellResolutionSource_isDGPretriangulated A D
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerve_isStable A _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotient_localKFlat A D P)

end SerrePositivity.InfinityCategories.Project.DerivedCategories

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite AGH "Prop A.1.5" (partial := special) "仮定：Lean が強い。前三角 dg 圏と選んだ部分圏の解消済み商。結論：その Verdier 商の nerve は安定（原典の安定性部分。任意の完全関手と写像スペクトル公式は別）。"] _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientNerve_isStable
