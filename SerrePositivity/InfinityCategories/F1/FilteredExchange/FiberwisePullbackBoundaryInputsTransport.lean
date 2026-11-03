module

public import SerrePositivity.InfinityCategories.Core.RightFibration
public import SerrePositivity.InfinityCategories.Core.VertexFiber
public import SerrePositivity.InfinityCategories.Core.VertexFiberMap
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.FiberwiseFunctorSpace
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.FiberwiseIntervalProjection
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.FiberwiseIntervalPullback
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.FiberwiseIntervalPullbackMaps
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.FiberwisePullbackBoundaryInputHomotopy
public import SerrePositivity.InfinityCategories.HomotopyLimits.FilteredExchange.FiberwisePullbackValue
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.IntervalDiagram
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.IntervalPullbackCoordinates
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.RelativeLeftFibrationTransport

/-!
概要：元の境界引き戻し射の全輸送を、二入力の全図式の相対輸送へ延長する。
方針：境界の左右射影を指定部分円柱として、二つの left fibration に持ち上げる。
規約：境界の二射影・全輸送円柱・底の全収縮を同時に厳密に保持する。
使われ方：全相対境界を持つ有限 path 模型の同時輸送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：境界の元の引き戻し輸送を保つ二入力の同時相対輸送。
方針：二つの fiber への相対輸送に境界の全円柱を指定する。
規約：境界の終点も全円柱も厳密に一致。使われ方：有限模型への全境界輸送の指定。 -/
lemma fiberwisePullback_boundary_inputs_transport {A K E D H B : SSet.{u}}
    (p : H ⟶ B) (f : E ⟶ H) (g : D ⟶ H)
    [LeftFibration (f ≫ p)] [LeftFibration (g ≫ p)] (i : A ⟶ K) [Mono i]
    (a : A ⟶ fiberwiseIntervalPullback p f g) (u : K ⟶ E) (v : K ⟶ D)
    (hu : i ≫ u = a ≫ fiberwiseIntervalPullbackLeft p f g)
    (hv : i ≫ v = a ≫ fiberwiseIntervalPullbackRight p f g)
    (b : B _⦋0⦌) (t : A ⟶ intervalPullback (vertexFiberMap (f ≫ p) p f rfl b)
      (vertexFiberMap (g ≫ p) p g rfl b))
    (L : SSet.Homotopy a (t ≫ fiberwisePullbackValueToTotal p f g b))
    (H₀ : SSet.Homotopy (u ≫ f ≫ p) (SSet.const b))
    (H₁ : SSet.Homotopy (v ≫ g ≫ p) (SSet.const b))
    (h₀ : (i ▷ (Δ[1] : SSet.{u})) ≫ H₀.h = L.h ≫ fiberwiseIntervalPullbackProjection p f g)
    (h₁ : (i ▷ (Δ[1] : SSet.{u})) ≫ H₁.h = L.h ≫ fiberwiseIntervalPullbackProjection p f g) :
    ∃ s : K ⟶ vertexFiber (f ≫ p) b, ∃ r : K ⟶ vertexFiber (g ≫ p) b,
      i ≫ s = t ≫ intervalPullbackLeft (vertexFiberMap (f ≫ p) p f rfl b)
        (vertexFiberMap (g ≫ p) p g rfl b) ∧
      i ≫ r = t ≫ intervalPullbackRight (vertexFiberMap (f ≫ p) p f rfl b)
        (vertexFiberMap (g ≫ p) p g rfl b) ∧
      ∃ U : SSet.Homotopy u (s ≫ vertexFiberι (f ≫ p) b),
      ∃ V : SSet.Homotopy v (r ≫ vertexFiberι (g ≫ p) b),
        (i ▷ (Δ[1] : SSet.{u})) ≫ U.h = L.h ≫ fiberwiseIntervalPullbackLeft p f g ∧
        (i ▷ (Δ[1] : SSet.{u})) ≫ V.h = L.h ≫ fiberwiseIntervalPullbackRight p f g ∧
        U.h ≫ (f ≫ p) = H₀.h ∧ V.h ≫ (g ≫ p) = H₁.h := by
  let U := fiberwisePullbackBoundaryLeftHomotopy p f g b a t L i u hu
  let V := fiberwisePullbackBoundaryRightHomotopy p f g b a t L i v hv
  have hp₀ : fiberwiseIntervalPullbackLeft p f g ≫ (f ≫ p) =
      fiberwiseIntervalPullbackProjection p f g := by
    simpa only [fiberwiseIntervalPullbackLeft, Category.assoc] using
      fiberwiseIntervalPullback_left_projection p f g
  have hp₁ : fiberwiseIntervalPullbackRight p f g ≫ (g ≫ p) =
      fiberwiseIntervalPullbackProjection p f g := by
    simpa only [fiberwiseIntervalPullbackRight, Category.assoc] using
      fiberwiseIntervalPullback_right_projection p f g
  have hUp : U.h ≫ (f ≫ p) = (i ▷ (Δ[1] : SSet.{u})) ≫ H₀.h := by
    change (L.h ≫ fiberwiseIntervalPullbackLeft p f g) ≫ (f ≫ p) = _
    rw [Category.assoc, hp₀, h₀]
  have hVp : V.h ≫ (g ≫ p) = (i ▷ (Δ[1] : SSet.{u})) ≫ H₁.h := by
    change (L.h ≫ fiberwiseIntervalPullbackRight p f g) ≫ (g ≫ p) = _
    rw [Category.assoc, hp₁, h₁]
  obtain ⟨s, hs, U', hU', hU'p⟩ := leftFibration_transport_to_fiber_relative (f ≫ p) i u b H₀
    (t ≫ intervalPullbackLeft _ _) U hUp
  obtain ⟨r, hr, V', hV', hV'p⟩ := leftFibration_transport_to_fiber_relative (g ≫ p) i v b H₁
    (t ≫ intervalPullbackRight _ _) V hVp
  exact ⟨s, r, hs, hr, U', V', hU', hV', hU'p, hV'p⟩

end SerrePositivity.InfinityCategories.F2
