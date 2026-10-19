module

public import SerrePositivity.KST.DerivedGeometry.AffineDerivedAdjunction
public import SerrePositivity.KST.DerivedGeometry.DerivedProducts
public import Mathlib.CategoryTheory.Triangulated.Adjunction

/-!
概要：非有界右導来大域切断の三角性と積保存。
方針：実際の導来随伴からシフトの両立・三角性・極限保存を導く。
規約：H の平坦性を要求しない。
使われ方：TT §3・§8、Toën §3.2、Stacks 36.3.3–36.3.5 の切断塔の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v₁ v₂
open CategoryTheory AlgebraicGeometry Limits
namespace SerrePositivity.KST.DerivedGeometry
variable {R : CommRingCat.{u}} (H : Type u) [Ring H] [Algebra R H]
  [HasDerivedCategory.{v₁} (ModuleCat.{u} H)]
  [HasDerivedCategory.{v₂} (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).Modules]

/--
概要：非有界右導来大域切断は加法的。
方針：加法的な tilde の右随伴であることを使う。
規約：実際の全係数層の導来圏。
使われ方：TT §3、Toën §3.2 の三角性。
-/
instance affineDerivedΓ_additive : (affineDerivedΓ (R := R) H).Additive :=
  (affineDerivedAdjunction (R := R) H).right_adjoint_additive

/--
概要：右導来大域切断は整数シフトと両立する。
方針：左随伴のシフト同型を随伴で移す。
規約：構成した随伴に付随するシフト同型。
使われ方：TT §3、Stacks 36.3.4 の切断三角。
-/
instance affineDerivedΓ_commShift : (affineDerivedΓ (R := R) H).CommShift ℤ :=
  (affineDerivedAdjunction (R := R) H).rightAdjointCommShift ℤ

/--
概要：アフィン導来随伴は整数シフトと両立する。
方針：随伴で移した右シフト構造の標準の両立性を使う。
規約：単位・余単位を含む両立性。
使われ方：TT §3、Toën §3.2 の導来随伴。
-/
instance affineDerivedAdjunction_commShift :
    (affineDerivedAdjunction (R := R) H).CommShift ℤ :=
  (affineDerivedAdjunction (R := R) H).commShift_of_leftAdjoint ℤ

/--
概要：右導来大域切断は三角関手。
方針：三角左随伴の右随伴の三角性を使う。
規約：非有界の区別三角を保存する。
使われ方：TT §3・§8、Toën §3.2、Stacks 36.3.4 の切断塔。
-/
instance affineDerivedΓ_isTriangulated : (affineDerivedΓ (R := R) H).IsTriangulated :=
  (affineDerivedAdjunction (R := R) H).isTriangulated_rightAdjoint

/--
概要：右導来大域切断は積を含む小さい極限を保存する。
方針：構成した導来随伴の右随伴の極限保存を使う。
規約：元の全係数層の導来圏で存在する極限についての保存。
使われ方：TT §3、Stacks 19.13.6・36.3.4 の導来逆極限の比較。
-/
instance affineDerivedΓ_preservesLimits :
    PreservesLimitsOfSize.{u, u} (affineDerivedΓ (R := R) H) :=
  (affineDerivedAdjunction (R := R) H).rightAdjoint_preservesLimits

end SerrePositivity.KST.DerivedGeometry
