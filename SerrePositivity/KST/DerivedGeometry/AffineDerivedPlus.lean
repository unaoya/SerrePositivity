module

public import SerrePositivity.KST.DerivedGeometry.AffineTildeAdjunctionExact
public import SerrePositivity.KST.DerivedGeometry.ExactDerivedPlusFactors
public import SerrePositivity.KST.DerivedGeometry.AffineDerivedTilde
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus

/-!
概要：実際の bounded below アフィン係数 tilde と右導来大域切断。
方針：既証の完全 tilde の導来化を制限し、大域切断の右導来関手を injective 分解から構成する。
規約：導来同値・単位同型は別定理として証明する。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 のアフィン導来比較の中間段階。
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
概要：bounded below 導来圏から元の全係数加群層の bounded below 導来圏への tilde。
方針：既証の完全な tilde の非有界導来化の制限を使う。
規約：標的を準連接複体の導来圏へ置換しない。
使われ方：TT §3、Toën §3.2 の bounded below アフィン比較の左関手。
-/
def affineDerivedTildePlus : DerivedCategory.Plus (ModuleCat.{u} H) ⥤
    DerivedCategory.Plus (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).Modules :=
  exactDerivedFunctorPlus (affineCoefficientTildeFunctor (R := R) H)

/--
概要：bounded below の係数 tilde は元の非有界 tilde と包含で可換。
方針：完全導来関手の制限の自然同型を適用する。
規約：自然な対象と射の比較を保持する。
使われ方：TT §3、Toën §3.2 の非有界比較へ向けた両立。
-/
def affineDerivedTildePlusSquare :
    affineDerivedTildePlus (R := R) H ⋙ DerivedCategory.Plus.ι ≅
      DerivedCategory.Plus.ι ⋙ affineDerivedTilde (R := R) H :=
  exactDerivedFunctorPlusSquare (affineCoefficientTildeFunctor (R := R) H)

/-- 概要：bounded below tilde は整数シフトと可換。方針：完全導来制限の構造を使う。
規約：標準のシフト。使われ方：TT §3、Toën §3.2 の三角比較。 -/
instance affineDerivedTildePlus_commShift : (affineDerivedTildePlus (R := R) H).CommShift ℤ :=
  by
  change (exactDerivedFunctorPlus (affineCoefficientTildeFunctor (R := R) H)).CommShift ℤ
  infer_instance

/-- 概要：bounded below tilde は三角関手。方針：完全導来制限の三角性を使う。
規約：同値はまだ主張しない。使われ方：TT §3、Toën §3.2 の導来比較。 -/
instance affineDerivedTildePlus_isTriangulated : (affineDerivedTildePlus (R := R) H).IsTriangulated :=
  by
  change (exactDerivedFunctorPlus (affineCoefficientTildeFunctor (R := R) H)).IsTriangulated
  infer_instance

/--
概要：全係数加群層の bounded below 導来圏から H 加群の bounded below 導来圏への右導来大域切断。
方針：元の係数加群層圏の十分な injective と Mathlib の右導来関手の構成を使う。
規約：H の平坦性を仮定しない。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 のアフィン比較の右関手。
-/
def affineDerivedΓPlus :
    DerivedCategory.Plus (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).Modules ⥤
      DerivedCategory.Plus (ModuleCat.{u} H) :=
  (affineCoefficientΓ (R := R) H).rightDerivedFunctorPlus

/-- 概要：bounded below 右導来大域切断は整数シフトと可換。方針：右導来関手の構造を使う。
規約：実際の右導来大域切断。使われ方：TT §3、Toën §3.2 の三角比較。 -/
instance affineDerivedΓPlus_commShift : (affineDerivedΓPlus (R := R) H).CommShift ℤ :=
  by
  change (affineCoefficientΓ (R := R) H).rightDerivedFunctorPlus.CommShift ℤ
  infer_instance

/-- 概要：bounded below 右導来大域切断は三角関手。方針：右導来関手の三角性を使う。
規約：元の係数層導来圏から構成する。使われ方：TT §3、Toën §3.2 の導来比較。 -/
instance affineDerivedΓPlus_isTriangulated : (affineDerivedΓPlus (R := R) H).IsTriangulated :=
  by
  change (affineCoefficientΓ (R := R) H).rightDerivedFunctorPlus.IsTriangulated
  infer_instance

end SerrePositivity.KST.DerivedGeometry
