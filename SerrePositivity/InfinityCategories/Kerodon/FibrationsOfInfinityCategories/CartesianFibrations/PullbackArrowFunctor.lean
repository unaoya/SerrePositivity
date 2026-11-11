module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.OverPullbackColimits
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.SquareColimitDescent

/-!
概要：固定した射影の底変換を底上の圏から射の圏への関手にする。
方針：既存の pullback の基礎関手と第一射影を射の圏へ束ねる。
規約：引き戻しは可変の底を第一因子に取る。
使われ方：底の余極限に沿う表現空間の降下。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：固定した射影の全ての底変換を射の圏の図式にする。
方針：pullback の基礎の関手の自然な射影を可換正方形に束ねる。
規約：全空間のモデルは pullback a.hom p。
使われ方：底上の図式の全空間と底の二つの余極限を同時に扱う。 -/
def transportPullbackArrowFunctor {E B : SSet.{u}} (p : E ⟶ B) : Over B ⥤ Arrow SSet.{u} where
  obj a := Arrow.mk (pullback.fst a.hom p)
  map f := Arrow.homMk ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying p).map f) f.left
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying_map_fst p f)
  map_id a := by
    apply Arrow.hom_ext
    · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying p).map_id a
    · rfl
  map_comp f g := by
    apply Arrow.hom_ext
    · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying p).map_comp f g
    · rfl

/-- 概要：底変換の関手の各可換正方形は pullback。
方針：pullback の自然な第一射影の既存の pullback 性を使う。
規約：底上の射は任意。
使われ方：表現条件を保存する関手の射の構成。 -/
lemma transportPullbackArrowFunctor_isPullback {E B : SSet.{u}} (p : E ⟶ B)
    {a b : Over B} (f : a ⟶ b) :
    IsPullback ((transportPullbackArrowFunctor p).map f).left
      ((transportPullbackArrowFunctor p).obj a).hom
      ((transportPullbackArrowFunctor p).obj b).hom
      ((transportPullbackArrowFunctor p).map f).right :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackProjection_isPullback p f

/-- 概要：底変換の図式の各射影は元の射影の left fibration 性を保つ。
方針：left fibration の底変換による閉性。
規約：可変の底を第一因子に取る。
使われ方：表現空間の底上の反変関手の定義。 -/
instance transportPullbackArrowFunctor_leftFibration {E B : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (a : Over B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration ((transportPullbackArrowFunctor p).obj a).hom :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrations.pullback_fst a.hom p (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem (p := p))⟩

/-- 概要：底上の余極限から得る四角形の制限錐は極限。
方針：底変換の余極限保存で全空間の余極限を得て四角形空間の降下へ適用する。
規約：添字は単体集合の宇宙で小さく、単射性は不要。
使われ方：pushout・非交和・骨格列の周囲の降下定理。 -/
def transportPullbackSquareColimitCone_isLimit {E B : SSet.{u + 1}}
    (p : E ⟶ B) {J : Type v} [Category.{w} J] [Small.{u + 1} J]
    {D : J ⥤ Over B} (c : Cocone D) (hc : IsColimit c) :
    IsLimit (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareColimitCone ((transportPullbackArrowFunctor p).mapCocone c)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareColimitCone_isLimit
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying_isColimit p c hc
  · exact isColimitOfPreserves (Over.forget B) hc

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
