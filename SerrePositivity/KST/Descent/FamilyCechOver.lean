module

public import SerrePositivity.KST.Descent.FamilyCechPresheafComparison
public import SerrePositivity.KST.Descent.PresheafBaseChange
public import SerrePositivity.KST.Descent.ZariskiCechLaw
public import SerrePositivity.KST.Descent.CechDescentComparison

/-!
# 被覆族の Over 上への実際の持ち上げ

## 概要
基底への構造射を持つ被覆族をスライス圏へ持ち上げ、元の前層の指定降下を移す。

## 方針
各被覆射を構造射と合成して Over の対象とし、忘却が connected な有限 wide pullback を保つことを使う。

## 規約
Over の忘却の終対象保存を仮定しない。元の増強元と各段の指定比較を保持する。

## 使われ方
論文 公理 (1)、補題 3.2 の自然な transfer の合成の局所検査。
原典の τ 位相の層論を Čech 計算で置換する。
-/

@[expose] public section

noncomputable section

universe u v z

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Opposite HomotopicalAlgebra AlgebraicGeometry
open SerrePositivity.Quillen

namespace SerrePositivity.KST.Descent

variable {C : Type u} [Category.{v} C] [HasFiniteLimits C]
  {ι : Type z} [Finite ι] {Y T : C} (q : T ⟶ Y) (X : ι → C) (cover : ∀ i, X i ⟶ T)

/-- 概要：被覆族の各成分を同じ構造射で Over に持ち上げる（公理 (1)）。
方針：被覆射と構造射の実際の合成を使う。
規約：元の対象は忘却で定義上戻る。使われ方：transfer の定義域。 -/
def familyOverObjects (i : ι) : Over Y := Over.mk (cover i ≫ q)

/-- 概要：Over 内の指定被覆射（公理 (1)）。
方針：元の被覆射を Over の射に束ねる。
規約：構造射の可換性は定義による。使われ方：Over 内の実際の Čech の各多重引き戻し。 -/
def familyOverCover (i : ι) : familyOverObjects q X cover i ⟶ Over.mk q :=
  Over.homMk (cover i) rfl

/-- 概要：Over の被覆族で制限した元の前層の図式は元の指定図式と同型（公理 (1)）。
方針：忘却の connected な極限の保存の実際の比較を適用する。
規約：増強元は元の対象の同じ値。使われ方：元の Zariski 降下の Over への移送。 -/
def familyOverPresheafSpaceIso (F : Cᵒᵖ ⥤ SSet.{0}) :
    familyCechSpace (familyOverObjects q X cover) (familyOverCover q X cover)
        (overPresheaf (Y := Y) F) ≅ familyCechSpace X cover F :=
  familyCechFunctorSpaceIso (Over.forget Y) (familyOverObjects q X cover)
    (familyOverCover q X cover) F

variable [ModelCategory SSet.{0}]
  (I J : MorphismProperty SSet.{0}) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{0} I J]

/-- 概要：元の被覆族の実降下は同じ構造射で持ち上げた Over の実降下を与える（公理 (1)）。
方針：指定増強を保持する実際の図式同型で降下を移す。
規約：余分な前層の法則は要求しない。使われ方：自然な transfer の合成の実降下による局所検査。 -/
theorem familyOverPresheafSpace_descent (F : Cᵒᵖ ⥤ SSet.{0})
    (hF : HasCechSpaceDescent SimplexCategory I J (familyCechSpace X cover F)) :
    HasCechSpaceDescent SimplexCategory I J
      (familyCechSpace (familyOverObjects q X cover) (familyOverCover q X cover)
        (overPresheaf (Y := Y) F)) :=
  (cechSpaceDescent_iso_iff SimplexCategory I J (familyOverPresheafSpaceIso q X cover F)).mpr hF

end SerrePositivity.KST.Descent
