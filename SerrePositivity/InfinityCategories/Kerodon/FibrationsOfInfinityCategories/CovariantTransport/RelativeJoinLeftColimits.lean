module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeJoinLeftFunctor
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.SSetPullbackColimit
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinLeftColimits
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-!
概要：relative join の左因子の連結な余極限の保存。
方針：通常の join の余極限に対して射影の pullback の正方形を使う。
規約：通常の単体集合の圏と Over 圏の余極限であり、空間の ∞ 余極限は主張しない。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、セルの族と骨格列に沿う比較の拡張。

対応節は Kerodon 5.2（Tag 019A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

/-- 概要：relative join の通常の join への第一射影を自然変換にまとめる。
方針：pullback の第一射影の計算則を自然性とする。
規約：底 S と右因子 Y→S を固定する。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、join の余極限の pullback。 -/
noncomputable def relativeJoinLeftProjection {Y S : SSet.{u}} (g : Y ⟶ S) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinLeftFunctor g ⟶ Over.forget S ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinLeftFunctor Y where
  app a := pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap a.hom g) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal S)
  naturality a b f := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinLeftMap_fst g f.left f.w

/-- 概要：左因子の連結な余極限を relative join へ写した cocone は余極限。
方針：通常の join へ写した cocone の各脚の pullback として表示する。
規約：形 J は宇宙 u で小さく連結とする。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、各次元のセルの族と可算の骨格。 -/
noncomputable def relativeJoin_left_isColimit {Y S : SSet.{u}} (g : Y ⟶ S)
    {J : Type v} [Category.{w} J] [Small.{u} J] [IsConnected J] {D : J ⥤ Over S}
    (c : Cocone D) (hc : IsColimit c) :
    IsColimit ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinLeftFunctor g).mapCocone c) := by
  let F := Over.forget S ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinLeftFunctor Y
  have hF : IsColimit (F.mapCocone c) := isColimitOfPreserves F hc
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.sset_isColimit_of_pullback (F.mapCocone c) hF
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinLeftFunctor g).mapCocone c)
    (Functor.whiskerLeft D (relativeJoinLeftProjection g))
    ((relativeJoinLeftProjection g).app c.pt)
  intro j
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinLeftMap_isPullback g (c.ι.app j).left (c.ι.app j).w

/-- 概要：固定した右因子の relative join は連結な余極限を保つ。
方針：任意の余極限 cocone に対する pullback の表示を使う。
規約：関手の始域は通常の Over S。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、比較を全ての始域へ拡張するセル分解。 -/
instance relativeJoinLeftFunctor_preservesConnectedColimits {Y S : SSet.{u}} (g : Y ⟶ S)
    (J : Type v) [Category.{w} J] [Small.{u} J] [IsConnected J] :
    PreservesColimitsOfShape J (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinLeftFunctor g) where
  preservesColimit := { preserves := fun hc ↦ ⟨relativeJoin_left_isColimit g _ hc⟩ }

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
