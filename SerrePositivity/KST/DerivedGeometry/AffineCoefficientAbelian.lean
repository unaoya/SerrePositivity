module

public import SerrePositivity.KST.DerivedGeometry.AffineCoefficientEquivalence
public import Mathlib.CategoryTheory.Abelian.Transfer

/-!
概要：アフィン準連接係数加群層のアーベル構造と大域切断の完全性。
方針：証明済みの加群圏との同値を使い、元の射の加法を保持する。
規約：全加群層の導来圏内の Dqc との比較は別定理。
使われ方：Toën §3.2、Bondal–van den Bergh Thm 3.1.1 のアフィン計算。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Limits AlgebraicGeometry
namespace SerrePositivity.KST.DerivedGeometry
variable {R : CommRingCat.{u}} (H : Type u) [Ring H] [Algebra R H]

/--
概要：アフィン準連接係数加群層の大域切断は加法的。
方針：部分圏の包含、切断の評価、スカラー制限の加法性を合成する。
規約：元の射の加法を保持する。
使われ方：Toën §3.2 の係数つきアフィン複体の比較。
-/
instance affineQcohΓ_additive : (affineQcohΓ (R := R) H).Additive where
  map_add := by intros; ext x; rfl

/--
概要：アフィン準連接係数加群層には小さい極限が存在する。
方針：加群圏への実際の同値から極限を移す。
規約：切断を開ごとに計算するとは主張しない。
使われ方：Toën §3.2 のアフィン準連接係数加群圏の完全構造。
-/
instance affineQcoh_hasLimits :
    HasLimitsOfSize.{u,u} (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).QCoh :=
  Adjunction.has_limits_of_equivalence (affineQcohΓ (R := R) H)

/--
概要：アフィン準連接係数加群層はアーベル圏。
方針：加群圏との同値で既存の加法構造にアーベル構造を構成する。
規約：係数の平坦性・可換性は不要。
使われ方：Toën §3.2、KST T1′ の係数複体を導来化する入力。
-/
instance affineQcoh_abelian :
    Abelian (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).QCoh :=
  abelianOfEquivalence (affineQcohΓ (R := R) H)

/--
概要：準連接対象に制限したアフィン大域切断は有限極限を保つ。
方針：証明済みの圏同値の極限保存を使う。
規約：全加群層の大域切断の完全性は主張しない。
使われ方：Toën §3.2 のアフィン複体のコホモロジー比較。
-/
instance affineQcohΓ_preservesFiniteLimits :
    PreservesFiniteLimits (affineQcohΓ (R := R) H) := inferInstance

/--
概要：準連接対象に制限したアフィン大域切断は有限余極限を保つ。
方針：証明済みの圏同値の余極限保存を使う。
規約：元の係数加群層の包含の完全性は別途確認する。
使われ方：Toën §3.2 のアフィン準連接複体の導来局所化。
-/
instance affineQcohΓ_preservesFiniteColimits :
    PreservesFiniteColimits (affineQcohΓ (R := R) H) := inferInstance

end SerrePositivity.KST.DerivedGeometry
