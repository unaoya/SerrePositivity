module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.IntervalPullbackLift
public import SerrePositivity.InfinityCategories.Core.EquivalencePathLifting
public import SerrePositivity.InfinityCategories.Core.HomotopyBoundaryExtension

/-!
概要：二入力と指定ホモトピーから元の path 引き戻しへの射を構成する。
方針：指定全円柱を curry し、三座標の持ち上げへ渡す。
規約：元の指定 path を選び直さない。
使われ方：指定 path の輸送と反映を引き戻し内の比較へ接続する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {K E D X : SSet.{u}} (f : E ⟶ X) (g : D ⟶ X)
  (u : K ⟶ E) (v : K ⟶ D) (H : SSet.Homotopy (u ≫ f) (v ≫ g))

/-- 概要：元の二入力と指定 path の族を path 引き戻しへ入れる。
方針：元の円柱を curry し両端条件を照合する。
規約：全単体パラメータで構成。使われ方：共通値での指定 path 検出。 -/
def intervalPullbackHomotopyPoint : K ⟶ intervalPullback f g :=
  intervalPullbackLift f g (curry ((β_ (Δ[1] : SSet.{u}) K).hom ≫ H.h)) u v
    (by
      change curry _ ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0) = u ≫ f
      rw [curry_evaluateFunctorAt_interval]
      exact H.h₀)
    (by
      change curry _ ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 1) = v ≫ g
      rw [curry_evaluateFunctorAt_interval]
      exact H.h₁)

/-- 概要：構成した射は指定全 path を保持する。
方針：持ち上げの射影。規約：全円柱。使われ方：比較の path 座標。 -/
lemma intervalPullbackHomotopyPoint_path :
    intervalPullbackHomotopyPoint f g u v H ≫ intervalPullbackPath f g =
      curry ((β_ (Δ[1] : SSet.{u}) K).hom ≫ H.h) :=
  intervalPullbackLift_path _ _ _ _ _ _ _

/-- 概要：構成した射は第一入力を保持する。
方針：持ち上げの射影。規約：元の u。使われ方：比較の第一座標。 -/
lemma intervalPullbackHomotopyPoint_left :
    intervalPullbackHomotopyPoint f g u v H ≫ intervalPullbackLeft f g = u :=
  intervalPullbackLift_left _ _ _ _ _ _ _

/-- 概要：構成した射は第二入力を保持する。
方針：持ち上げの射影。規約：元の v。使われ方：比較の第二座標。 -/
lemma intervalPullbackHomotopyPoint_right :
    intervalPullbackHomotopyPoint f g u v H ≫ intervalPullbackRight f g = v :=
  intervalPullbackLift_right _ _ _ _ _ _ _

end SerrePositivity.InfinityCategories.F2
