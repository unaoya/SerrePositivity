module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.StrictConeReindex
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
概要：span の反対の添字と標準 cospan の添字を厳密に比較する。
方針：歩く span の反対の標準圏同値を AsSmall の忘却と持ち上げで挟む。
規約：元の span の左脚は cospan の左脚に対応する。
使われ方：HTT 4.2.4.1、homotopy 押し出しを反変 Hom の引き戻しで判定する。

対応節は Kerodon 7.5（Tag 039Y）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits

local instance oppositeSpanCospanThin (X Y : AsSmall.{u} WalkingCospan) :
    Subsingleton (X ⟶ Y) :=
  inferInstanceAs (Subsingleton (ULift.{u} (AsSmall.down.obj X ⟶ AsSmall.down.obj Y)))

local instance oppositeSpanSpanThin (X Y : AsSmall.{u} WalkingSpan) :
    Subsingleton (X ⟶ Y) :=
  inferInstanceAs (Subsingleton (ULift.{u} (AsSmall.down.obj X ⟶ AsSmall.down.obj Y)))

/-- 概要：標準 cospan の添字を標準 span の反対へ写す関手。
方針：歩く span の反対の圏同値の逆を持ち上げる。
規約：左右の端を交換せず使う。
使われ方：押し出しの反変 Hom を既存の cospan 比較へ渡す。 -/
def oppositeSpanIndex : AsSmall.{u} WalkingCospan ⥤ (AsSmall.{u} WalkingSpan)ᵒᵖ :=
  AsSmall.down ⋙ walkingSpanOpEquiv.inverse ⋙ AsSmall.up.op

/-- 概要：標準 cospan と標準 span の反対の持ち上げた添字の圏同値。
方針：標準の双対の圏同値の両向きを持ち上げ、恒等成分で単位・余単位を与える。
規約：通常の Hom 錐の極限性の移送に使う。
使われ方：Kerodon 7.5.4.6（Tag 03BB）、元の押し出しの Hom の普遍性。 -/
def oppositeSpanIndexEquivalence :
    AsSmall.{u} WalkingCospan ≌ (AsSmall.{u} WalkingSpan)ᵒᵖ where
  functor := oppositeSpanIndex
  inverse := AsSmall.down.op ⋙ walkingSpanOpEquiv.functor ⋙ AsSmall.up
  unitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intro _ _ _; apply Subsingleton.elim)
  counitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intro _ _ _; apply Subsingleton.elim)

/-- 概要：標準 cospan から span の反対への添字関手の nerve は厳密な同型。
方針：圏同値の逆の nerve を逆射とし、対象と薄い Hom を比較する。
規約：native な極限性の移送に必要な同型性を明示する。
使われ方：HTT 4.2.4.1、反対の Hom 錐を標準 cospan として判定する。 -/
instance nerveMap_oppositeSpanIndex_isIso : IsIso (nerveMap oppositeSpanIndex.{u}) := by
  let H := oppositeSpanIndexEquivalence.{u}.inverse
  refine ⟨nerveMap H, ?_, ?_⟩
  all_goals
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
    intro i j f
    exact Subsingleton.elim _ _

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
