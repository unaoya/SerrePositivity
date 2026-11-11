module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.VertexFiber
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.VertexFiberMap
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiberwiseFunctorFiber
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiberwiseFunctorSpace
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiberwiseIntervalProjection
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiberwiseIntervalPullback
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiberwiseIntervalPullbackMaps
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiberwisePullbackFiberCoordinates

/-!
概要：path 引き戻しの fiber への射は元の値の三座標で一意に決まる。
方針：path の fiber 同型を消去し、元の全空間の三座標の一意性へ戻す。
規約：同じ底の頂点を固定する。
使われ方：元の値の path 引き戻しとの同型の往復。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 概要：fiber への射は元の値の path と二入力で決まる。
方針：fiber の単射な包含後に元の path 引き戻しの三座標を検査する。
規約：全 path を保持。使われ方：fiber 比較の厳密な一意性。 -/
lemma fiberwisePullbackFiber_hom_ext {T E D H B : SSet.{u}}
    (p : H ⟶ B) (f : E ⟶ H) (g : D ⟶ H) (b : B _⦋0⦌)
    {a c : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullbackProjection p f g) b}
    (hp : a ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackFiberPath p f g b = c ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackFiberPath p f g b)
    (hl : a ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackFiberLeft p f g b = c ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackFiberLeft p f g b)
    (hr : a ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackFiberRight p f g b = c ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackFiberRight p f g b) :
    a = c := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullbackProjection p f g) b
  apply _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseIntervalPullback_hom_ext p f g
  · simp only [_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackFiberPath, ← Category.assoc] at hp
    have hh := (cancel_mono (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseFunctorFiberIso p Δ[1] b).hom).1 hp
    have h := congrArg (fun z ↦ z ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwiseFunctorProjection p Δ[1]) b) hh
    simpa only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_ι] using h
  · have h := congrArg (fun z ↦ z ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (f ≫ p) b) hl
    simpa only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackFiberLeft_ι] using h
  · have h := congrArg (fun z ↦ z ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (g ≫ p) b) hr
    simpa only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberwisePullbackFiberRight_ι] using h

end SerrePositivity.InfinityCategories.Project.FilteredExchange
