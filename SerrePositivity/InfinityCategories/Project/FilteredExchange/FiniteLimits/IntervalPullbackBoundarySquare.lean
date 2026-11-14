module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.PrismContraction
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.CoproductCylinderMap
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.CylinderBoundaryMono
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.IntervalDiagram
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.IntervalPullbackCoordinates
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.IntervalPullbackHomotopyPoint
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.IntervalPullbackHomotopySquare
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.IntervalPullbackLift
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.PathSquareCurry
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.PathSquareEndHomotopy

/-!
概要：全境界輸送の指定された path 正方形を、三座標を保つ引き戻し内の比較へ移す。
方針：直和境界の両枝を制限し、終端 path と引き戻し内のホモトピーを構成する。
規約：二入力の全輸送と元の path 正方形を厳密に保持する。
使われ方：一般 coherent filtered 引き戻しの標的側の有限検出。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 概要：元の全境界輸送に整合する path 正方形は引き戻し内の指定比較を与える。
方針：両枝の側辺を読み、三座標の円柱を持ち上げる。
規約：終端 path の全円柱も保持。使われ方：指定 path を保つ同時有限検出。 -/
lemma intervalPullback_homotopy_of_boundary_square {K E D X : SSet.{u}}
    (f : E ⟶ X) (g : D ⟶ X) {u₀ u₁ : K ⟶ E} {v₀ v₁ : K ⟶ D}
    (H₀ : SSet.Homotopy (u₀ ≫ f) (v₀ ≫ g))
    (U : SSet.Homotopy u₀ u₁) (V : SSet.Homotopy v₀ v₁)
    {b : K ⊗ (Δ[1] : SSet.{u}) ⟶ X} (G : SSet.Homotopy H₀.h b)
    (hG : (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.cylinderBoundaryInclusion K ▷ (Δ[1] : SSet.{u})) ≫ G.h =
      _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coprodCylinderMap (U.h ≫ f) (V.h ≫ g)) :
    ∃ H₁ : SSet.Homotopy (u₁ ≫ f) (v₁ ≫ g), H₁.h = b ∧
      ∃ L : SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackHomotopyPoint f g u₀ v₀ H₀)
        (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackHomotopyPoint f g u₁ v₁ H₁),
        L.h ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackLeft f g = U.h ∧
        L.h ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackRight f g = V.h ∧
        L.h ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackPath f g = _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.pathSquareCurry G.h := by
  have h₀ : ((SSet.ι₀ : K ⟶ K ⊗ (Δ[1] : SSet.{u})) ▷ (Δ[1] : SSet.{u})) ≫ G.h =
      U.h ≫ f := by
    have h := congrArg (fun r ↦ ((coprod.inl : K ⟶ K ⨿ K) ▷ (Δ[1] : SSet.{u})) ≫ r) hG
    rw [← comp_whiskerRight_assoc, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.cylinderBoundaryInclusion, coprod.inl_desc,
      _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coprodCylinderMap_inl] at h
    exact h
  have h₁ : ((SSet.ι₁ : K ⟶ K ⊗ (Δ[1] : SSet.{u})) ▷ (Δ[1] : SSet.{u})) ≫ G.h =
      V.h ≫ g := by
    have h := congrArg (fun r ↦ ((coprod.inr : K ⟶ K ⨿ K) ▷ (Δ[1] : SSet.{u})) ≫ r) hG
    rw [← comp_whiskerRight_assoc, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.cylinderBoundaryInclusion, coprod.inr_desc,
      _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coprodCylinderMap_inr] at h
    exact h
  have hp₀ : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.pathSquareCurry G.h ≫ (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalEndpointNatTrans 0).app X = U.h ≫ f := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.pathSquareCurry_endpoint]; exact h₀
  have hp₁ : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.pathSquareCurry G.h ≫ (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalEndpointNatTrans 1).app X = V.h ≫ g := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.pathSquareCurry_endpoint]; exact h₁
  let H₁ := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.pathSquareEndHomotopy f g U V G h₀ h₁
  let L := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackHomotopyOfSquare f g H₀ H₁ U V G h₀ h₁
  refine ⟨H₁, rfl, L, ?_, ?_, ?_⟩
  · exact _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackLift_left f g (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.pathSquareCurry G.h) U.h V.h hp₀ hp₁
  · exact _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackLift_right f g (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.pathSquareCurry G.h) U.h V.h hp₀ hp₁
  · exact _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalPullbackLift_path f g (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.pathSquareCurry G.h) U.h V.h hp₀ hp₁

end SerrePositivity.InfinityCategories.Project.FilteredExchange
