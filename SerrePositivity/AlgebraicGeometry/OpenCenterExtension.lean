module

public import SerrePositivity.AlgebraicGeometry.Flattening
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
概要：KST §5、Stacks 080Y のアフィン開集合上の admissible 中心の基底全体への延長。
方針：準コンパクトな開埋め込みによるイデアル層の像を取り、開基底変換で核を計算する。
規約：延長は実際の IdealSheafData.map を使い、元の中心への制限を証明する。
使われ方：局所的な支配中心の有限個の共通細分による大域化。
-/

@[expose] public noncomputable section

universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits

set_option backward.isDefEq.respectTransparency false in
/--
概要：準コンパクトな開埋め込みで延長した中心を元の開集合へ戻すと、元の中心に一致する。
方針：開埋め込みの単射性によるファイバー積と開基底変換の核の公式を使う。
規約：KST §5、Stacks 080Y、イデアル層の実際の等式。
使われ方：アフィン局所の blowup 中心を全体へ延長する。
-/
theorem idealSheaf_comap_map_openImmersion {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] [QuasiCompact j] (K : X.IdealSheafData) :
    (K.map j).comap j = K := by
  have H : IsPullback K.subschemeι (𝟙 K.subscheme) j (K.subschemeι ≫ j) :=
    IsPullback.of_vert_isIso_mono ⟨by simp⟩
  apply Scheme.IdealSheafData.ext
  funext U
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
  have hker := Scheme.ker_ideal_of_isPullback_of_isOpenImmersion
    (K.subschemeι ≫ j) K.subschemeι (𝟙 K.subscheme) j H U
  rw [K.ker_subschemeι] at hker
  exact hker.symm

set_option backward.isDefEq.respectTransparency false in
/--
概要：U の逆像を避ける中心の準コンパクトな射による延長も U を避ける。
方針：延長中心の支持は像の閉包であり、U の閉補集合がその像を含むことを使う。
規約：KST §5、Stacks 080Y、この支持の主張自体に開埋め込み性は不要。
使われ方：局所的な admissible 中心の大域延長。
-/
theorem isUAdmissibleCenter_map {X Y : Scheme.{u}} (j : X ⟶ Y) [QuasiCompact j]
    (U : Y.Opens) (K : X.IdealSheafData) (hK : IsUAdmissibleCenter (j ⁻¹ᵁ U) K) :
    IsUAdmissibleCenter U (K.map j) := by
  have hsub : j '' (K.support : Set X) ⊆ (U.compl : Set Y) := by
    rintro _ ⟨x, hxK, rfl⟩
    change j x ∉ U
    intro hxU
    exact hK hxU hxK
  have hc := closure_minimal hsub U.compl.isClosed
  intro x hxU hxK
  rw [Scheme.IdealSheafData.support_map] at hxK
  exact hc hxK hxU

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
