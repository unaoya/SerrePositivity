module
public import SerrePositivity.KST.NonConnective.DGKappaSuspension
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGQuotientPretriangulated
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGPerfectYonedaIdempotentCompletion

/-!
概要：同じ実平坦懸垂と、その元の Perf 値をつなぐ dg Yoneda の完備化性を保持する。
方針：D 正本の平坦商の前三角性と、同じ Yoneda の native 冪等完備化を使う。
規約：同じ明示 I に条件付き。完備化を同値や通常の局所化とは主張しない。
使われ方：K-7 c5 の完備化前の実商と固定 ν の Perf 値を区別する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (D : PerfDGInput.{u, max (u + 1) v} R)
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)

/-- 概要：同じ実平坦 Drinfeld 懸垂は dg 前三角性を持つ。
方針：同じ cone の cell 平坦源に D 正本の商の前三角性を適用する。
規約：同じ I と同じ零化対象集合を保持する。
使われ方：元の実商の dg Yoneda 完備化への代入。 -/
theorem dgKappaSuspension_isDGPretriangulated :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R (dgKappaSuspensionKInput R D I) := by
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellResolutionSource_isDGPretriangulated R (DGKappaCone R D I)
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotient_isDGPretriangulated R
    (DGCategoryCellResolution.Source R (DGKappaCone R D I))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGNullObjects R (DGKappaCone R D I) (dgKappaConePerfectObjects R D I))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotient_localKFlat R (DGKappaCone R D I) (dgKappaConePerfectObjects R D I))

/-- 概要：元の実平坦懸垂からその Perf への元の Yoneda は native 冪等完備化である。
方針：同じ実商の前三角性を D 正本の Yoneda 完備化へ代入する。
規約：同じ I に条件付き。同値性・K₀ 全射性・固定 ν 上の Verdier 認証は含めない。
使われ方：完備化前の fibration と、完備化後の実 K 比較を分けて検証する。 -/
theorem dgKappaSuspensionYoneda_isIdempotentCompletion :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectYonedaInfinity R (dgKappaSuspensionKInput R D I)) := by
  let := dgKappaSuspension_isDGPretriangulated R D I
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectYonedaInfinity_isIdempotentCompletion R (dgKappaSuspensionKInput R D I)

end SerrePositivity.KST.NonConnective
