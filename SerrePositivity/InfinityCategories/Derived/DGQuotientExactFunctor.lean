module
public import SerrePositivity.InfinityCategories.Derived.DGPretriangulatedFunctorExact
public import SerrePositivity.InfinityCategories.Derived.ResolvedDGQuotientStability

/-! # 実 dg 商関手の完全性

概要：前三角 dg 圏の局所 K-flat な商射影と平坦分解後の商関手は完全。
方針：前三角 dg 関手の native nerve の完全性を実包含へ適用し、分解の逆と合成する。
規約：局所化の全 ∞ 関手圏での普遍性は別工程。使われ方：β3 の Verdier 列。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v)
  [DGCategory A D] [Small.{u} D] [IsDGPretriangulated A D]

/-- 局所 K-flat な前三角 dg 圏の実商射影は零対象と全 cofiber 列を保つ。 -/
theorem dgQuotientNerveProjection_isExactFunctor
    (P : Set D) (h : DGQuotient.localKFlat A D P) :
    IsExactFunctor (dgQuotientNerveProjection A D P) := by
  let := dgQuotient_isDGPretriangulated A D P h
  exact dgPretriangulatedFunctor_isExactFunctor A D (DGQuotient.QuotientObject D P)
    (DGQuotient.inclusion A D P)

/-- 元の Hom の平坦性を仮定せず、平坦分解後の実商射影は完全。 -/
theorem resolvedDGQuotientProjection_isExactFunctor (P : Set D) :
    IsExactFunctor (resolvedDGQuotientProjection A D P) := by
  let := dgCellResolutionSource_isDGPretriangulated A D
  exact dgQuotientNerveProjection_isExactFunctor A _ _ (resolvedDGQuotient_localKFlat A D P)

/-- 平坦分解の逆を通る、元の dg nerve から実商への関手は完全。 -/
theorem resolvedDGQuotientFunctor_isExactFunctor (P : Set D) :
    IsExactFunctor (resolvedDGQuotientFunctor A D P) := by
  let := resolvedDGQuotientProjection_isExactFunctor A D P
  let : IsExactFunctor (dgCellResolutionNerveEquivalence A D).inv :=
    isExactFunctor_of_isQCatEquivalence
      (dgCellResolutionNerveEquivalence A D).symm.isQCatEquivalence
  exact isExactFunctor_comp _ _

end SerrePositivity.InfinityCategories
