module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.PrismContraction
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.IntervalDiagram
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.IntervalPullbackCoordinates
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.IntervalPullbackHomotopyPoint
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.IntervalPullbackLift
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.PathSquareCurry

/-!
概要：二入力の輸送と整合する指定 path の変形から、path 引き戻し内のホモトピーを作る。
方針：path の変形を curry し、二入力の全円柱とともに三座標を持ち上げる。
規約：三つの全円柱を選び直さず保持する。
使われ方：元の有限 path 模型の同時輸送を標的の引き戻し内の実際の比較へ移す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange
variable {K E D X : SSet.{u}} (f : E ⟶ X) (g : D ⟶ X)
  {u₀ u₁ : K ⟶ E} {v₀ v₁ : K ⟶ D}
  (H₀ : SSet.Homotopy (u₀ ≫ f) (v₀ ≫ g)) (H₁ : SSet.Homotopy (u₁ ≫ f) (v₁ ≫ g))
  (U : SSet.Homotopy u₀ u₁) (V : SSet.Homotopy v₀ v₁)
  (G : SSet.Homotopy H₀.h H₁.h)
  (h₀ : ((SSet.ι₀ : K ⟶ K ⊗ (Δ[1] : SSet.{u})) ▷ (Δ[1] : SSet.{u})) ≫ G.h = U.h ≫ f)
  (h₁ : ((SSet.ι₁ : K ⟶ K ⊗ (Δ[1] : SSet.{u})) ▷ (Δ[1] : SSet.{u})) ≫ G.h = V.h ≫ g)

/-- 概要：指定四辺の整合する正方形は引き戻し内の実際のホモトピーを与える。
方針：三座標の円柱を持ち上げ、両端を三座標の一意性で同定する。
規約：充填性は不要。使われ方：共通値への同時輸送と指定 path の比較。 -/
def intervalPullbackHomotopyOfSquare :
    SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackHomotopyPoint f g u₀ v₀ H₀)
      (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackHomotopyPoint f g u₁ v₁ H₁) := by
  have hp₀ : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.pathSquareCurry G.h ≫ (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalEndpointNatTrans 0).app X = U.h ≫ f := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.pathSquareCurry_endpoint]
    exact h₀
  have hp₁ : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.pathSquareCurry G.h ≫ (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalEndpointNatTrans 1).app X = V.h ≫ g := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.pathSquareCurry_endpoint]
    exact h₁
  let R := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackLift f g (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.pathSquareCurry G.h) U.h V.h hp₀ hp₁
  refine ⟨R, ?_, ?_, ?_⟩
  · change SSet.ι₀ ≫ R = _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackHomotopyPoint f g u₀ v₀ H₀
    apply _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullback_hom_ext f g
    · dsimp only [R]
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackLift_path, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.pathSquareCurry_zero,
        _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackHomotopyPoint_path, G.h₀]
    · dsimp only [R]
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackLift_left, U.h₀,
        _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackHomotopyPoint_left]
    · dsimp only [R]
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackLift_right, V.h₀,
        _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackHomotopyPoint_right]
  · change SSet.ι₁ ≫ R = _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackHomotopyPoint f g u₁ v₁ H₁
    apply _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullback_hom_ext f g
    · dsimp only [R]
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackLift_path, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.pathSquareCurry_one,
        _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackHomotopyPoint_path, G.h₁]
    · dsimp only [R]
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackLift_left, U.h₁,
        _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackHomotopyPoint_left]
    · dsimp only [R]
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackLift_right, V.h₁,
        _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackHomotopyPoint_right]
  · apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

end SerrePositivity.InfinityCategories.Project.FilteredExchange
