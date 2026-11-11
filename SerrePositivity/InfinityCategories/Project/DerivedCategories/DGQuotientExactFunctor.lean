module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGPretriangulatedFunctorExact
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ResolvedDGQuotientStability

/-! # 実 dg 商関手の完全性

概要：前三角 dg 圏の局所 K-flat な商射影と平坦分解後の商関手は完全。
方針：前三角 dg 関手の native nerve の完全性を実包含へ適用し、分解の逆と合成する。
規約：局所化の全 ∞ 関手圏での普遍性は別工程。使われ方：β3 の Verdier 列。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v)
  [DGCategory A D] [Small.{u} D] [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]

/-- 局所 K-flat な前三角 dg 圏の実商射影は零対象と全 cofiber 列を保つ。 -/
theorem dgQuotientNerveProjection_isExactFunctor
    (P : Set D) (h : DGQuotient.localKFlat A D P) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection A D P) := by
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotient_isDGPretriangulated A D P h
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPretriangulatedFunctor_isExactFunctor A D (DGQuotient.QuotientObject D P)
    (DGQuotient.inclusion A D P)

/-- 元の Hom の平坦性を仮定せず、平坦分解後の実商射影は完全。 -/
theorem resolvedDGQuotientProjection_isExactFunctor (P : Set D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientProjection A D P) := by
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellResolutionSource_isDGPretriangulated A D
  exact dgQuotientNerveProjection_isExactFunctor A _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotient_localKFlat A D P)

/-- 平坦分解の逆を通る、元の dg nerve から実商への関手は完全。 -/
theorem resolvedDGQuotientFunctor_isExactFunctor (P : Set D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientFunctor A D P) := by
  let := resolvedDGQuotientProjection_isExactFunctor A D P
  let : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellResolutionNerveEquivalence A D).inv :=
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_isQCatEquivalence
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellResolutionNerveEquivalence A D).symm.isQCatEquivalence
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.isExactFunctor_comp _ _

end SerrePositivity.InfinityCategories.Project.DerivedCategories
