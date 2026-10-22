module

public import SerrePositivity.InfinityCategories.F2.Idempotent.PointSliceArrows
public import SerrePositivity.InfinityCategories.F2.Idempotent.LeftFibrationRetracts

/-!
概要：元の辺は、両端点を retract から拡大した辺の全関手 ∞ 圏内の retract。
方針：終点固定の右 fibration と始点固定の左 fibration に順に持ち上げる。
規約：retract は元の全辺の関手 ∞ 圏内のもの。端点の分解だけに弱めない。
使われ方：完備化の任意の辺の fiber/cofiber の存在の準備。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 始点の指定 retract は、終点を固定した全辺の関手 ∞ 圏内の retract に持ち上がる。 -/
lemma arrow_source_retract_lift {X : SSet.{u}} [Quasicategory X]
    (a : (Δ[1] : SSet.{u}) ⟶ X) (x : X _⦋0⦌)
    (r : VertexRetraction (SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 2) ≫ a)) x) :
    ∃ b : (Δ[1] : SSet.{u}) ⟶ X,
      SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 2) ≫ b) = x ∧
      stdSimplex.δ (0 : Fin 2) ≫ b = stdSimplex.δ (0 : Fin 2) ≫ a ∧
      IsVertexRetractOf (functorVertex a) (functorVertex b) := by
  let p := stdSimplex.δ (0 : Fin 2) ≫ a
  have hv : (arrowPointCone a).vertex =
      SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 2) ≫ a) := by
    change SSet.yonedaEquiv (joinInl Δ[0] Δ[0] ≫ ((joinStdSimplexIso 0 0).hom ≫ a)) = _
    rw [← Category.assoc, joinStdSimplexIso_zero_inl]
  obtain ⟨z, hz, hr⟩ := rightFibration_retract_lift (sliceOverProjection p)
    (arrowPointCone a) x (by
      change VertexRetraction (arrowPointCone a).vertex x
      rw [hv]
      exact r)
  let b := (joinStdSimplexIso 0 0).inv ≫ z.val
  refine ⟨b, ?_, pointSliceArrow_target z, ?_⟩
  · have h := congrArg SSet.yonedaEquiv (pointSliceArrow_source z)
    rw [Equiv.apply_symm_apply] at h
    exact h.trans hz
  · have h := hr.map (pointSliceArrowMap p)
    rw [pointSliceArrowMap_arrowPointCone, pointSliceArrowMap_vertex] at h
    exact h

/-- 終点の指定 retract は、始点を固定した全辺の関手 ∞ 圏内の retract に持ち上がる。 -/
lemma arrow_target_retract_lift {X : SSet.{u}} [Quasicategory X]
    (a : (Δ[1] : SSet.{u}) ⟶ X) (y : X _⦋0⦌)
    (r : VertexRetraction (SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2) ≫ a)) y) :
    ∃ b : (Δ[1] : SSet.{u}) ⟶ X,
      stdSimplex.δ (1 : Fin 2) ≫ b = stdSimplex.δ (1 : Fin 2) ≫ a ∧
      SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2) ≫ b) = y ∧
      IsVertexRetractOf (functorVertex a) (functorVertex b) := by
  let p := stdSimplex.δ (1 : Fin 2) ≫ a
  have hv : (arrowPointCocone a).vertex =
      SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2) ≫ a) := by
    change SSet.yonedaEquiv (joinInr Δ[0] Δ[0] ≫ ((joinStdSimplexIso 0 0).hom ≫ a)) = _
    rw [← Category.assoc, joinStdSimplexIso_zero_inr]
  obtain ⟨z, hz, hr⟩ := leftFibration_retract_lift (sliceUnderProjection p)
    (arrowPointCocone a) y (by
      change VertexRetraction (arrowPointCocone a).vertex y
      rw [hv]
      exact r)
  let b := (joinStdSimplexIso 0 0).inv ≫ z.val
  refine ⟨b, pointCosliceArrow_source z, ?_, ?_⟩
  · have h := congrArg SSet.yonedaEquiv (pointCosliceArrow_target z)
    rw [Equiv.apply_symm_apply] at h
    exact h.trans hz
  · have h := hr.map (pointCosliceArrowMap p)
    rw [pointCosliceArrowMap_arrowPointCocone, pointCosliceArrowMap_vertex] at h
    exact h

/-- 両端の指定 retract は、同じ全辺の関手 ∞ 圏内の一つの retract を与える。 -/
lemma arrow_retract_lift {X : SSet.{u}} [Quasicategory X]
    (a : (Δ[1] : SSet.{u}) ⟶ X) (x y : X _⦋0⦌)
    (rx : VertexRetraction (SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 2) ≫ a)) x)
    (ry : VertexRetraction (SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2) ≫ a)) y) :
    ∃ b : (Δ[1] : SSet.{u}) ⟶ X,
      SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 2) ≫ b) = x ∧
      SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2) ≫ b) = y ∧
      IsVertexRetractOf (functorVertex a) (functorVertex b) := by
  obtain ⟨c, hcx, hcy, hac⟩ := arrow_source_retract_lift a x rx
  have rcy : VertexRetraction (SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2) ≫ c)) y := by
    rw [hcy]
    exact ry
  obtain ⟨b, hbc, hby, hcb⟩ := arrow_target_retract_lift c y rcy
  exact ⟨b, (congrArg SSet.yonedaEquiv hbc).trans hcx, hby, hac.trans hcb⟩

end SerrePositivity.InfinityCategories.F2.Idempotent
