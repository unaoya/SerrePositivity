module

public import SerrePositivity.InfinityCategories.F1.RelativeJoinLeftFunctor
public import SerrePositivity.InfinityCategories.F1.SSetPullbackColimit
public import SerrePositivity.InfinityCategories.Core.JoinLeftColimits
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-!
概要：relative join の左因子の連結な余極限の保存。
方針：通常の join の余極限に対して射影の pullback の正方形を使う。
規約：通常の単体集合の圏と Over 圏の余極限であり、空間の ∞ 余極限は主張しない。
使われ方：Kerodon Proposition 5.2.4.5、セルの族と骨格列に沿う比較の拡張。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：relative join の通常の join への第一射影を自然変換にまとめる。
方針：pullback の第一射影の計算則を自然性とする。
規約：底 S と右因子 Y→S を固定する。
使われ方：Kerodon Proposition 5.2.4.5、join の余極限の pullback。 -/
noncomputable def relativeJoinLeftProjection {Y S : SSet.{u}} (g : Y ⟶ S) :
    relativeJoinLeftFunctor g ⟶ Over.forget S ⋙ joinLeftFunctor Y where
  app a := pullback.fst (joinMap a.hom g) (joinDiagonal S)
  naturality a b f := relativeJoinLeftMap_fst g f.left f.w

/-- 概要：左因子の連結な余極限を relative join へ写した cocone は余極限。
方針：通常の join へ写した cocone の各脚の pullback として表示する。
規約：形 J は宇宙 u で小さく連結とする。
使われ方：Kerodon Proposition 5.2.4.5、各次元のセルの族と可算の骨格。 -/
noncomputable def relativeJoin_left_isColimit {Y S : SSet.{u}} (g : Y ⟶ S)
    {J : Type v} [Category.{w} J] [Small.{u} J] [IsConnected J] {D : J ⥤ Over S}
    (c : Cocone D) (hc : IsColimit c) :
    IsColimit ((relativeJoinLeftFunctor g).mapCocone c) := by
  let F := Over.forget S ⋙ joinLeftFunctor Y
  have hF : IsColimit (F.mapCocone c) := isColimitOfPreserves F hc
  apply sset_isColimit_of_pullback (F.mapCocone c) hF
    ((relativeJoinLeftFunctor g).mapCocone c)
    (Functor.whiskerLeft D (relativeJoinLeftProjection g))
    ((relativeJoinLeftProjection g).app c.pt)
  intro j
  exact relativeJoinLeftMap_isPullback g (c.ι.app j).left (c.ι.app j).w

/-- 概要：固定した右因子の relative join は連結な余極限を保つ。
方針：任意の余極限 cocone に対する pullback の表示を使う。
規約：関手の始域は通常の Over S。
使われ方：Kerodon Proposition 5.2.4.5、比較を全ての始域へ拡張するセル分解。 -/
instance relativeJoinLeftFunctor_preservesConnectedColimits {Y S : SSet.{u}} (g : Y ⟶ S)
    (J : Type v) [Category.{w} J] [Small.{u} J] [IsConnected J] :
    PreservesColimitsOfShape J (relativeJoinLeftFunctor g) where
  preservesColimit := { preserves := fun hc ↦ ⟨relativeJoin_left_isColimit g _ hc⟩ }

end SerrePositivity.InfinityCategories
