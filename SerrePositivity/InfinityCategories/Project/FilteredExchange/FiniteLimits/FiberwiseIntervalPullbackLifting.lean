module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.FiberwiseFunctorSpace
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.FiberwiseIntervalEndpointPair
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.FiberwiseIntervalProjection
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.FiberwiseIntervalPullback
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.FiberwiseIntervalPullbackMaps
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.FiberwiseIntervalPullbackSquare
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.FiberwisePullbackInputPair

/-!
概要：fiber ごとの path 引き戻しの二入力射と底射は left fibration。
方針：相対両端評価の底変換と、入力の底射との合成を使う。
規約：入力の底射は元の f ≫ p と g ≫ p。
使われ方：引き戻し全空間の元の有限図式と境界を同じ fiber で検出する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 概要：元の二入力を指定した path の族は、二入力の組への left fibration。
方針：底を固定した相対両端評価を引き戻す。
規約：元の二入力を保持。使われ方：両端を保つ相対ホーンの充填。 -/
instance fiberwisePullbackInputPair_leftFibration {E D H B : SSet.{u}}
    (p : H ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (f : E ⟶ H) (g : D ⟶ H) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackInputPair p f g) := by
  let h := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullback_isPullback p f g
  refine ⟨?_⟩
  rw [← h.isoPullback_hom_snd]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrations.comp_mem _ _ (MorphismProperty.of_isIso _ h.isoPullback.hom)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrations.pullback_snd _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem (p := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalEndpointPair p)))

/-- 概要：元の三全空間が同じ底上の left fibration なら path 引き戻しもそうなる。
方針：二入力射、入力積の第一射影、元の入力の底射を合成する。
規約：共有する元の底射そのもの。使われ方：filtered な底の相対有限検出の適用。 -/
instance fiberwiseIntervalPullbackProjection_leftFibration {E D H B : SSet.{u}}
    (p : H ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (f : E ⟶ H) (g : D ⟶ H)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (f ≫ p)] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (g ≫ p)] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullbackProjection p f g) := by
  have hfst : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (pullback.fst (f ≫ p) (g ≫ p)) :=
    ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrations.pullback_fst _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem (p := g ≫ p))⟩
  have he : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackInputPair p f g ≫
      (pullback.fst (f ≫ p) (g ≫ p) ≫ (f ≫ p)) =
      _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullbackProjection p f g := by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackInputPair_fst]
    exact _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullback_left_projection p f g
  refine ⟨?_⟩
  rw [← he]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrations.comp_mem _ _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem (p := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackInputPair p f g))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrations.comp_mem _ _ hfst.mem (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem (p := f ≫ p)))

end SerrePositivity.InfinityCategories.Project.FilteredExchange
