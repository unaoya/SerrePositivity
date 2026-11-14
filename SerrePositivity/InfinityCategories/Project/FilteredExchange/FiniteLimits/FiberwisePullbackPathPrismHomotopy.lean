module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.PrismContraction
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.FiberwiseIntervalProjection
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.FiberwiseIntervalPullback
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.FiberwiseIntervalPullbackMaps
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.FiberwisePullbackPathPrism

/-!
概要：元の引き戻し内の輸送から、指定全 path の輸送正方形を読む。
方針：輸送の全円柱を path 方向に評価し、四端と底射を計算する。
規約：path は左、輸送時間は右。三座標の全輸送を厳密に保持する。
使われ方：相対 path 境界の指定輸送を有限模型の相対持ち上げへ渡す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange
variable {A E D H B : SSet.{u}} (p : H ⟶ B) (f : E ⟶ H) (g : D ⟶ H)
  {a c : A ⟶ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullback p f g} (L : SSet.Homotopy a c)

/-- 概要：引き戻し内の全輸送は、元の全 path の間の実際の輸送正方形を与える。
方針：全円柱を path 変数で評価し、時間端点の自然性を使う。
規約：元の全円柱を保持。使われ方：指定境界 path の輸送。 -/
def fiberwisePullbackPathPrismHomotopy :
    SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackPathPrism p f g a) (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackPathPrism p f g c) where
  h := (α_ (Δ[1] : SSet.{u}) A (Δ[1] : SSet.{u})).hom ≫
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackPathPrism p f g L.h
  h₀ := by
    change ((Δ[1] : SSet.{u}) ◁ SSet.ι₀) ≫
      _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackPathPrism p f g L.h = _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackPathPrism p f g a
    rw [← _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackPathPrism_precomp, L.h₀]
  h₁ := by
    change ((Δ[1] : SSet.{u}) ◁ SSet.ι₁) ≫
      _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackPathPrism p f g L.h = _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackPathPrism p f g c
    rw [← _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackPathPrism_precomp, L.h₁]
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

/-- 概要：path 始点上の正方形は元の第一入力の輸送の像。
方針：path 始点評価を全円柱へ適用する。
規約：全時間。使われ方：相対境界の第一端の貼り合わせ。 -/
lemma fiberwisePullbackPathPrismHomotopy_zero :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ▷ (Δ[1] : SSet.{u})) ≫
      (fiberwisePullbackPathPrismHomotopy p f g L).h =
        L.h ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullbackLeft p f g ≫ f := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (A ⊗ (Δ[1] : SSet.{u})) ≫
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackPathPrism p f g L.h = _
  exact _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackPathPrism_zero p f g L.h

/-- 概要：path 終点上の正方形は元の第二入力の輸送の像。
方針：path 終点評価を全円柱へ適用する。
規約：全時間。使われ方：相対境界の第二端の貼り合わせ。 -/
lemma fiberwisePullbackPathPrismHomotopy_one :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ▷ (Δ[1] : SSet.{u})) ≫
      (fiberwisePullbackPathPrismHomotopy p f g L).h =
        L.h ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullbackRight p f g ≫ g := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (A ⊗ (Δ[1] : SSet.{u})) ≫
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackPathPrism p f g L.h = _
  exact _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackPathPrism_one p f g L.h

/-- 概要：全 path 正方形の底は元の底輸送を path 方向に定値にしたもの。
方針：評価円柱の底の式を全輸送へ適用する。
規約：全時間の厳密な因子分解。使われ方：有限模型の指定境界の相対輸送。 -/
lemma fiberwisePullbackPathPrismHomotopy_projection :
    (fiberwisePullbackPathPrismHomotopy p f g L).h ≫ p =
      (snd (Δ[1] : SSet.{u}) A ▷ (Δ[1] : SSet.{u})) ≫
        L.h ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullbackProjection p f g := by
  change ((α_ (Δ[1] : SSet.{u}) A (Δ[1] : SSet.{u})).hom ≫
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackPathPrism p f g L.h) ≫ p = _
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackPathPrism_projection]
  rfl

end SerrePositivity.InfinityCategories.Project.FilteredExchange
