module

public import SerrePositivity.KST.DerivedGeometry.AffineDerivedPlus
public import SerrePositivity.KST.DerivedGeometry.DerivedPlusAdjunction

/-!
概要：実際の係数加群層の bounded below 導来圏上の tilde と右導来大域切断の随伴。
方針：完全 tilde と全層の大域切断の随伴を複体と導来局所化へ移す。
規約：導来単位の同型性・本質的全射性は別の定理として証明する。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の係数アフィン導来比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory AlgebraicGeometry
namespace SerrePositivity.KST.DerivedGeometry
variable {R : CommRingCat.{u}} (H : Type u) [Ring H] [Algebra R H]
  [HasDerivedCategory (ModuleCat.{u} H)]
  [HasDerivedCategory (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).Modules]

/--
概要：bounded below のアフィン係数 tilde は元の全係数層圏の右導来大域切断の左随伴。
方針：実際の通常随伴と元の係数層の injective 分解による右導来の普遍性を用いる。
規約：H の可換性・平坦性を要求しない。非有界同値とは別の主張。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 のアフィン導来比較。
-/
def affineDerivedPlusAdjunction :
    affineDerivedTildePlus (R := R) H ⊣ affineDerivedΓPlus (R := R) H :=
  derivedPlusAdjunction (affineCoefficientTildeAdjunction (R := R) H)

end SerrePositivity.KST.DerivedGeometry
