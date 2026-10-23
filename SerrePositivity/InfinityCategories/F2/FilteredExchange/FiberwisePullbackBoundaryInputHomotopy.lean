module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FiberwisePullbackValueCoordinates

/-!
概要：元の境界引き戻し射の輸送から、二入力の指定輸送を全円柱ごと読む。
方針：元の二射影を後合成し、値の包含の座標式で終点を照合する。
規約：元の境界輸送の全円柱を選び直さない。
使われ方：単射な境界を保つ二入力の相対 fiber 輸送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {A K E D H B : SSet.{u}} (p : H ⟶ B) (f : E ⟶ H) (g : D ⟶ H) (b : B _⦋0⦌)
  (a : A ⟶ fiberwiseIntervalPullback p f g)
  (t : A ⟶ intervalPullback (vertexFiberMap (f ≫ p) p f rfl b)
    (vertexFiberMap (g ≫ p) p g rfl b))
  (L : SSet.Homotopy a (t ≫ fiberwisePullbackValueToTotal p f g b))

/-- 概要：境界輸送の第一入力への射影は、元の第一 fiber の指定円柱。
方針：元の第一射影の後合成を全円柱として保持する。
規約：始点の境界式も指定。使われ方：第一入力の相対輸送の指定部分円柱。 -/
def fiberwisePullbackBoundaryLeftHomotopy (i : A ⟶ K) (u : K ⟶ E)
    (hu : i ≫ u = a ≫ fiberwiseIntervalPullbackLeft p f g) :
    SSet.Homotopy (i ≫ u)
      ((t ≫ intervalPullbackLeft (vertexFiberMap (f ≫ p) p f rfl b)
        (vertexFiberMap (g ≫ p) p g rfl b)) ≫ vertexFiberι (f ≫ p) b) where
  h := L.h ≫ fiberwiseIntervalPullbackLeft p f g
  h₀ := by
    change SSet.ι₀ ≫ (L.h ≫ fiberwiseIntervalPullbackLeft p f g) = i ≫ u
    rw [← Category.assoc, L.h₀, hu]
  h₁ := by
    change SSet.ι₁ ≫ (L.h ≫ fiberwiseIntervalPullbackLeft p f g) = _
    rw [← Category.assoc, L.h₁, Category.assoc, fiberwisePullbackValueToTotal_left]
    rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

/-- 概要：境界輸送の第二入力への射影は、元の第二 fiber の指定円柱。
方針：元の第二射影の後合成を全円柱として保持する。
規約：始点の境界式も指定。使われ方：第二入力の相対輸送の指定部分円柱。 -/
def fiberwisePullbackBoundaryRightHomotopy (i : A ⟶ K) (v : K ⟶ D)
    (hv : i ≫ v = a ≫ fiberwiseIntervalPullbackRight p f g) :
    SSet.Homotopy (i ≫ v)
      ((t ≫ intervalPullbackRight (vertexFiberMap (f ≫ p) p f rfl b)
        (vertexFiberMap (g ≫ p) p g rfl b)) ≫ vertexFiberι (g ≫ p) b) where
  h := L.h ≫ fiberwiseIntervalPullbackRight p f g
  h₀ := by
    change SSet.ι₀ ≫ (L.h ≫ fiberwiseIntervalPullbackRight p f g) = i ≫ v
    rw [← Category.assoc, L.h₀, hv]
  h₁ := by
    change SSet.ι₁ ≫ (L.h ≫ fiberwiseIntervalPullbackRight p f g) = _
    rw [← Category.assoc, L.h₁, Category.assoc, fiberwisePullbackValueToTotal_right]
    rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

end SerrePositivity.InfinityCategories.F2
