module

public import SerrePositivity.KST.DerivedGeometry.CoefficientExact

/-!
# 係数加群層の自由・忘却随伴

概要：構造層から係数環層へのスカラー拡大とスカラー制限の随伴を構成する。
方針：恒等な基礎空間上の加群層の引き戻し・押し出しを使う。
規約：層の圏での随伴であり、左導来関手は別途構成する。
使われ方：KST T1、Bondal–van den Bergh Thm 3.1.1 の係数版、Toën §3.2。
-/

@[expose] public section

noncomputable section

set_option maxSynthPendingDepth 8
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry

namespace SerrePositivity.KST.DerivedGeometry.CoefficientSheaf

variable {X : Scheme.{u}} (B : CoefficientSheaf X)

/--
概要：係数忘却には層の圏で左随伴が存在する。
方針：恒等な基礎空間に沿う加群層の押し出しの右随伴性を使う。
規約：平坦性は不要だが、左随伴の完全性は主張しない。
使われ方：KST T1、Toën §3.2 の自由係数加群層の構成。
-/
instance forget_isRightAdjoint : B.forget.IsRightAdjoint :=
  inferInstanceAs ((SheafOfModules.pushforward.{u}
    (F := 𝟭 (TopologicalSpace.Opens X)) B.structureMap).IsRightAdjoint)

/--
概要：構造層の加群層から自由係数加群層を作る関手。
方針：実在する係数忘却の左随伴を取る。
規約：導来化前の層の関手。非平坦係数では複体へそのまま適用して導来化しない。
使われ方：KST T1、Toën §3.2 の自由・忘却随伴の左側。
-/
def free : X.Modules ⥤ B.Modules := B.forget.leftAdjoint

/--
概要：層の圏での自由・忘却随伴。
方針：係数忘却の右随伴性から単位・余単位を構成する。
規約：随伴の存在を仮定するフィールドは追加しない。
使われ方：KST T1、Bondal–van den Bergh Thm 3.1.1 の係数版の導来随伴の入力。
-/
def freeForgetAdjunction : B.free ⊣ B.forget :=
  Adjunction.ofIsRightAdjoint B.forget

/--
概要：自由係数加群層の構成は左随伴。
方針：構成した随伴から関手の性質を取り出す。
規約：層の関手に関する性質。
使われ方：KST T1、Toën §3.2 の自由関手による余極限の保存。
-/
instance free_isLeftAdjoint : B.free.IsLeftAdjoint :=
  B.freeForgetAdjunction.isLeftAdjoint

end SerrePositivity.KST.DerivedGeometry.CoefficientSheaf
