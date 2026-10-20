module

public import SerrePositivity.InfinityCategories.F2.FiberwiseIntervalPullbackLift
public import SerrePositivity.InfinityCategories.F2.FiberwiseIntervalProjection
public import SerrePositivity.InfinityCategories.Core.EquivalencePathLifting

/-!
概要：元の fiber ごとの path 引き戻し射から、指定全 path の評価円柱を読む。
方針：元の path 射影を uncurry し、両端と共有底を計算する。
規約：path は第一因子、底は path 変数に定値。
使われ方：境界の元の引き戻し射と有限 path 模型の同時輸送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {A E D H B : SSet.{u}} (p : H ⟶ B) (f : E ⟶ H) (g : D ⟶ H)
  (a : A ⟶ fiberwiseIntervalPullback p f g)

/-- 概要：元の path 引き戻し射の全 path の評価。
方針：path 射影を uncurry する。規約：全単体を保持。使われ方：指定境界 path の表示。 -/
def fiberwisePullbackPathPrism : (Δ[1] : SSet.{u}) ⊗ A ⟶ H :=
  uncurry (a ≫ fiberwiseIntervalPullbackPath p f g ≫
    pullback.fst ((ihom (Δ[1] : SSet.{u})).map p) (constantDiagram Δ[1] B))

/-- 概要：評価円柱の始点は元の第一入力の像。
方針：curry の評価と始点の条件。規約：元の f。使われ方：相対境界の貼り合わせ。 -/
lemma fiberwisePullbackPathPrism_zero :
    prismEndpoint 0 A ≫ fiberwisePullbackPathPrism p f g a =
      a ≫ fiberwiseIntervalPullbackLeft p f g ≫ f := by
  rw [fiberwisePullbackPathPrism, ← curry_evaluateFunctorAt_interval, curry_uncurry]
  change (a ≫ fiberwiseIntervalPullbackPath p f g) ≫ fiberwiseIntervalEndpoint p 0 = _
  rw [Category.assoc, fiberwiseIntervalPullbackPath_zero]

/-- 概要：評価円柱の終点は元の第二入力の像。
方針：curry の評価と終点の条件。規約：元の g。使われ方：相対境界の貼り合わせ。 -/
lemma fiberwisePullbackPathPrism_one :
    prismEndpoint 1 A ≫ fiberwisePullbackPathPrism p f g a =
      a ≫ fiberwiseIntervalPullbackRight p f g ≫ g := by
  rw [fiberwisePullbackPathPrism, ← curry_evaluateFunctorAt_interval, curry_uncurry]
  change (a ≫ fiberwiseIntervalPullbackPath p f g) ≫ fiberwiseIntervalEndpoint p 1 = _
  rw [Category.assoc, fiberwiseIntervalPullbackPath_one]

/-- 概要：評価円柱の底は共有底射を path 変数に定値にしたもの。
方針：fiber ごとの関手の評価の底射を前合成する。
規約：全 path 上の厳密な式。使われ方：底の有限押し出し上の収縮の構成。 -/
lemma fiberwisePullbackPathPrism_projection :
    fiberwisePullbackPathPrism p f g a ≫ p =
      snd (Δ[1] : SSet.{u}) A ≫ a ≫ fiberwiseIntervalPullbackProjection p f g := by
  rw [fiberwisePullbackPathPrism, ← Category.assoc, uncurry_natural_left, Category.assoc,
    fiberwiseFunctorUncurry_projection]
  rfl

/-- 概要：評価円柱はパラメータの前合成に自然。
方針：uncurry の自然性。規約：path 全体を保つ。使われ方：輸送の時間端点の制限。 -/
lemma fiberwisePullbackPathPrism_precomp {C : SSet.{u}} (i : C ⟶ A) :
    fiberwisePullbackPathPrism p f g (i ≫ a) =
      ((Δ[1] : SSet.{u}) ◁ i) ≫ fiberwisePullbackPathPrism p f g a := by
  simp only [fiberwisePullbackPathPrism, Category.assoc, uncurry_natural_left]

end SerrePositivity.InfinityCategories.F2
