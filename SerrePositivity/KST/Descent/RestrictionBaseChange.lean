module

public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# 開部分上の同型性の実際の底変換での保存

## 概要
ある開部分上で同型なスキーム射を任意の射へ底変換すると、逆像の開部分上でも同型になる。

## 方針
実際の Cartesian 正方形を四つの開部分へ制限し、同型射の底変換を使う。

## 規約
指定された引き戻しの第二射影とその実際の開制限を使う。

## 使われ方
論文 補題 3.3 の抽象 blowup 正方形を Čech 各段に底変換する幾何入力。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace SerrePositivity.KST.Descent

set_option backward.isDefEq.respectTransparency false in
/-- 概要：指定開部分上での同型性は任意の底変換で逆像開部分上の同型性を与える（補題 3.3）。
方針：実際の引き戻しを開制限し、右側の同型性を第二射影へ移す。
規約：スキームの実際の制限射についての同型性。
使われ方：抽象 blowup の中心外同型条件を Čech 各段へ移す。 -/
theorem pullback_snd_iso_over_open {X Y T : Scheme.{u}} (p : X ⟶ Y) (h : T ⟶ Y)
    (U : Y.Opens) [IsIso (p ∣_ U)] :
    IsIso (pullback.snd p h ∣_ (h ⁻¹ᵁ U)) := by
  have he : pullback.fst p h ⁻¹ᵁ p ⁻¹ᵁ U = pullback.snd p h ⁻¹ᵁ h ⁻¹ᵁ U :=
    congrArg (fun k ↦ k ⁻¹ᵁ U) (pullback.condition (f := p) (g := h))
  have hpre : pullback.snd p h ⁻¹ᵁ h ⁻¹ᵁ U =
      (pullback.fst p h ⁻¹ᵁ p ⁻¹ᵁ U) ⊓ (pullback.snd p h ⁻¹ᵁ h ⁻¹ᵁ U) := by
    rw [he, inf_idem]
  have H := Scheme.Hom.isPullback_resLE (IsPullback.of_hasPullback p h)
    (US := U) (UT := h ⁻¹ᵁ U) (UX := p ⁻¹ᵁ U) le_rfl le_rfl hpre
  have hp : IsIso (p.resLE U (p ⁻¹ᵁ U) le_rfl) := by
    rw [Scheme.Hom.resLE_eq_morphismRestrict]
    infer_instance
  have hs := H.isIso_snd_of_isIso hp
  simpa only [Scheme.Hom.resLE_eq_morphismRestrict] using hs

end SerrePositivity.KST.Descent
