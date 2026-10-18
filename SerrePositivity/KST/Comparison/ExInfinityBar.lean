module

public import SerrePositivity.KST.Comparison.BarLocalizedEquivalence
public import SerrePositivity.KST.Comparison.ExInfinityGrouplike

/-!
# 元の bar と Kan モノイドの bar の比較

概要：単体的モノイドの Ex∞ 置換は bar 分類空間の局所化可逆な比較射を与える。
方針：基礎射が Ex∞ の単位であることと、bar の局所化不変性を使う。
規約：Segal 1974 Proposition 1.5 の Kan な模型への移行。Segal のファイバー比較そのものは残項目。
使われ方：群状モノイドの bar の比較を Kan なモノイドで計算する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory
open SerrePositivity.SimplicialModel

/--
概要：単体的モノイドの Ex∞ 置換が誘導する bar の比較射は局所化で可逆である。
方針：基礎単体集合の単位の可逆性と bar の局所化不変性を使う。
規約：群状性はこの比較には不要で、置換後の群状性は ExInfinityGrouplike で証明済み。
使われ方：元の群状モノイドの分類空間を Kan なモノイドの分類空間へ移す。
-/
instance exInfinitySimplicialMonoid_bar_localized_isIso (M : SimplicialObject MonCat.{u}) :
    IsIso (AnodyneHomotopy.anodyneQ.map (monoidBarMap (exInfinitySimplicialMonoidUnit.app M))) :=
  monoidBarMap_localized_isIso (exInfinitySimplicialMonoidUnit.app M) inferInstance

end SerrePositivity.KST.Comparison
