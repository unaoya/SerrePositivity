module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.AffineModels
public import SerrePositivity.AlgebraicGeometry.BlowupLocalization

/-!
概要：KST §5 のイデアル層の局所 blowup モデルの基本開集合への制限。
方針：構造層の基本開集合上の局所化条件を Rees blowup の局所化へ移す。
規約：中心はイデアル層の切断イデアルの等式で同定する。
使われ方：一般スキーム上の局所モデル間の開埋め込みと貼り合わせ。
-/

@[expose] public noncomputable section

universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory
variable {X : Scheme.{u}} (I : X.IdealSheafData)

set_option backward.isDefEq.respectTransparency false in
/--
概要：アフィン基本開集合への局所 blowup 比較射は開埋め込み。
方針：制限写像が係数の一元局所化であることと、イデアル層の制限の像の等式を使う。
規約：KST §5、基礎スキームは任意。
使われ方：アフィン局所モデルを開部分スキームとして貼り合わせる。
-/
instance affineBlowupModelMap_basicOpen_isOpenImmersion {V : X.affineOpens}
    (f : Γ(X, V.1)) : IsOpenImmersion (affineBlowupModelMap I (X.affineBasicOpen_le f)) := by
  let : Algebra Γ(X, V.1) Γ(X, X.basicOpen f) :=
    (affineModelRestriction (X.affineBasicOpen_le f)).toAlgebra
  have : IsLocalization.Away f Γ(X, X.basicOpen f) :=
    V.2.isLocalization_of_eq_basicOpen _ _ rfl
  exact affineBlowupCenterMap_isOpenImmersion
    (R := Γ(X, V.1)) (S := Γ(X, X.basicOpen f)) (I.ideal V) f
    (I.ideal (X.affineBasicOpen f)) (I.map_ideal (X.affineBasicOpen_le f))

set_option backward.isDefEq.respectTransparency false in
/--
概要：基本開集合への局所モデル比較の像は構造射によるその基本開集合の逆像。
方針：切断環の局所化の場合の像を、アフィン開集合の切断環との同型で移送する。
規約：KST §5、点集合の像の等式として述べる。
使われ方：任意のアフィン開集合の包含への比較を局所的に調べる。
-/
theorem affineBlowupModelMap_basicOpen_range {V : X.affineOpens} (f : Γ(X, V.1)) :
    Set.range (affineBlowupModelMap I (X.affineBasicOpen_le f)) =
      (affineBlowupModelToBase I V ⁻¹ᵁ X.basicOpen f).carrier := by
  let : Algebra Γ(X, V.1) Γ(X, X.basicOpen f) :=
    (affineModelRestriction (X.affineBasicOpen_le f)).toAlgebra
  have : IsLocalization.Away f Γ(X, X.basicOpen f) :=
    V.2.isLocalization_of_eq_basicOpen _ _ rfl
  rw [affineBlowupModelToBase_preimage_basicOpen]
  exact affineBlowupCenterMap_range
    (R := Γ(X, V.1)) (S := Γ(X, X.basicOpen f)) (I.ideal V) f
    (I.ideal (X.affineBasicOpen f)) (I.map_ideal (X.affineBasicOpen_le f))

set_option backward.isDefEq.respectTransparency false in
/--
概要：基本開集合と等しいアフィン開集合の包含に沿うモデル比較も開埋め込み。
方針：アフィン開集合の等式で基本開集合の場合へ移す。
規約：KST §5、包含の証明には依存しない。
使われ方：二つのアフィン開集合の共通の基本開近傍。
-/
theorem affineBlowupModelMap_isOpenImmersion_of_eq_basicOpen {U V : X.affineOpens}
    (h : U ≤ V) (f : Γ(X, V.1)) (hU : U = X.affineBasicOpen f) :
    IsOpenImmersion (affineBlowupModelMap I h) := by
  subst U
  exact affineBlowupModelMap_basicOpen_isOpenImmersion I f

set_option backward.isDefEq.respectTransparency false in
/--
概要：基本開集合と等しいアフィン開集合へのモデル比較の像を同定する。
方針：アフィン開集合の等式で基本開集合の像の公式へ移す。
規約：KST §5、点集合の像の等式。
使われ方：共通の基本開近傍から局所モデルの点を持ち上げる。
-/
theorem affineBlowupModelMap_range_of_eq_basicOpen {U V : X.affineOpens}
    (h : U ≤ V) (f : Γ(X, V.1)) (hU : U = X.affineBasicOpen f) :
    Set.range (affineBlowupModelMap I h) =
      (affineBlowupModelToBase I V ⁻¹ᵁ X.basicOpen f).carrier := by
  subst U
  exact affineBlowupModelMap_basicOpen_range I f

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
