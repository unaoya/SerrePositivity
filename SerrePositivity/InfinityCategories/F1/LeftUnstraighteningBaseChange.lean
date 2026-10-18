module

public import SerrePositivity.InfinityCategories.F1.LeftUnstraightening
public import SerrePositivity.InfinityCategories.F1.LeftFibrationBaseChange

/-!
概要：coherent diagram の制限の unstraightening と、元の fibration の底変換との同型。
方針：既存の unstraightening の引き戻し四角形から標準引き戻しとの同型を取る。
規約：通常の単体集合と Over 圏の同型であり、∞ 極限の主張ではない。
使われ方：Kerodon Remark 5.6.2.5、分類の対象における底変換の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：制限した coherent diagram の unstraightening は元の射影の引き戻しと同型。
方針：unstraightening の底変換四角形の普遍性を使う。
規約：元の図式の定義域は B、制限後の定義域は D。
使われ方：Kerodon Remark 5.6.2.5、底変換の全空間の具体的な比較。 -/
noncomputable def leftUnstraighteningBaseChangeIso {B D : SSet.{u + 1}}
    (F : B ⟶ SpaceInfinity.{u}) (k : D ⟶ B) :
    leftUnstraightening (k ≫ F) ≅ pullback (leftUnstraighteningProjection F) k :=
  (leftUnstraighteningMap_isPullback (k ≫ F) F k rfl).isoPullback

/-- 概要：底変換の同型の第一射影は既存の unstraightening の比較射。
方針：引き戻しの普遍同型の第一射影公式を適用する。
規約：比較射は元の底の射 k を被覆する。
使われ方：Kerodon Remark 5.6.2.5、対象の比較を全空間の射へ移す計算。 -/
lemma leftUnstraighteningBaseChangeIso_hom_fst {B D : SSet.{u + 1}}
    (F : B ⟶ SpaceInfinity.{u}) (k : D ⟶ B) :
    (leftUnstraighteningBaseChangeIso F k).hom ≫
      pullback.fst (leftUnstraighteningProjection F) k =
        leftUnstraighteningMap (k ≫ F) F k rfl :=
  IsPullback.isoPullback_hom_fst _

/-- 概要：底変換の同型は制限後の底 D を厳密に保つ。
方針：引き戻しの普遍同型の第二射影公式を適用する。
規約：射影は leftUnstraighteningProjection で表示する。
使われ方：Kerodon Remark 5.6.2.5、底上の対象の同型への移行。 -/
lemma leftUnstraighteningBaseChangeIso_hom_snd {B D : SSet.{u + 1}}
    (F : B ⟶ SpaceInfinity.{u}) (k : D ⟶ B) :
    (leftUnstraighteningBaseChangeIso F k).hom ≫
      pullback.snd (leftUnstraighteningProjection F) k =
        leftUnstraighteningProjection (k ≫ F) :=
  IsPullback.isoPullback_hom_snd _

/-- 概要：unstraightening と底変換の比較を底上の対象の同型として表す。
方針：全空間の同型と第二射影の整合性から Over 圏の同型を作る。
規約：同型の両対象はともに D 上の left fibration の射影。
使われ方：Kerodon Remark 5.6.2.5、相対関手空間を比較する際の底上の同型。 -/
noncomputable def leftUnstraighteningBaseChangeOverIso {B D : SSet.{u + 1}}
    (F : B ⟶ SpaceInfinity.{u}) (k : D ⟶ B) :
    Over.mk (leftUnstraighteningProjection (k ≫ F)) ≅
      (leftFibrationBaseChangeObject k
        (leftFibrationObjectOf (leftUnstraighteningProjection F))).val :=
  Over.isoMk (leftUnstraighteningBaseChangeIso F k)
    (leftUnstraighteningBaseChangeIso_hom_snd F k)

end SerrePositivity.InfinityCategories
