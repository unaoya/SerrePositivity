module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.PointSliceArrows
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.LeftFibrationRetracts

/-!
概要：元の辺は、両端点を retract から拡大した辺の全関手 ∞ 圏内の retract。
方針：終点固定の右 fibration と始点固定の左 fibration に順に持ち上げる。
規約：retract は元の全辺の関手 ∞ 圏内のもの。端点の分解だけに弱めない。
使われ方：完備化の任意の辺の fiber/cofiber の存在の準備。

対応節は Kerodon 8.5（Tag 03Y9）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents

/-- 始点の指定 retract は、終点を固定した全辺の関手 ∞ 圏内の retract に持ち上がる。 -/
lemma arrow_source_retract_lift {X : SSet.{u}} [Quasicategory X]
    (a : (Δ[1] : SSet.{u}) ⟶ X) (x : X _⦋0⦌)
    (r : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.VertexRetraction (SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 2) ≫ a)) x) :
    ∃ b : (Δ[1] : SSet.{u}) ⟶ X,
      SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 2) ≫ b) = x ∧
      stdSimplex.δ (0 : Fin 2) ≫ b = stdSimplex.δ (0 : Fin 2) ≫ a ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsVertexRetractOf (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex b) := by
  let p := stdSimplex.δ (0 : Fin 2) ≫ a
  have hv : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.arrowPointCone a).vertex =
      SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 2) ≫ a) := by
    change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[0] Δ[0] ≫ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom ≫ a)) = _
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.joinStdSimplexIso_zero_inl]
  obtain ⟨z, hz, hr⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.rightFibration_retract_lift (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.arrowPointCone a) x (by
      change _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.VertexRetraction (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.arrowPointCone a).vertex x
      rw [hv]
      exact r)
  let b := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫ z.val
  refine ⟨b, ?_, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.pointSliceArrow_target z, ?_⟩
  · have h := congrArg SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.pointSliceArrow_source z)
    rw [Equiv.apply_symm_apply] at h
    exact h.trans hz
  · have h := hr.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.pointSliceArrowMap p)
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.pointSliceArrowMap_arrowPointCone, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.pointSliceArrowMap_vertex] at h
    exact h

/-- 終点の指定 retract は、始点を固定した全辺の関手 ∞ 圏内の retract に持ち上がる。 -/
lemma arrow_target_retract_lift {X : SSet.{u}} [Quasicategory X]
    (a : (Δ[1] : SSet.{u}) ⟶ X) (y : X _⦋0⦌)
    (r : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.VertexRetraction (SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2) ≫ a)) y) :
    ∃ b : (Δ[1] : SSet.{u}) ⟶ X,
      stdSimplex.δ (1 : Fin 2) ≫ b = stdSimplex.δ (1 : Fin 2) ≫ a ∧
      SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2) ≫ b) = y ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsVertexRetractOf (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex b) := by
  let p := stdSimplex.δ (1 : Fin 2) ≫ a
  have hv : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.arrowPointCocone a).vertex =
      SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2) ≫ a) := by
    change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] Δ[0] ≫ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom ≫ a)) = _
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.joinStdSimplexIso_zero_inr]
  obtain ⟨z, hz, hr⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.leftFibration_retract_lift (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.arrowPointCocone a) y (by
      change _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.VertexRetraction (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.arrowPointCocone a).vertex y
      rw [hv]
      exact r)
  let b := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫ z.val
  refine ⟨b, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.pointCosliceArrow_source z, ?_, ?_⟩
  · have h := congrArg SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.pointCosliceArrow_target z)
    rw [Equiv.apply_symm_apply] at h
    exact h.trans hz
  · have h := hr.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.pointCosliceArrowMap p)
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.pointCosliceArrowMap_arrowPointCocone, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.pointCosliceArrowMap_vertex] at h
    exact h

/-- 両端の指定 retract は、同じ全辺の関手 ∞ 圏内の一つの retract を与える。 -/
lemma arrow_retract_lift {X : SSet.{u}} [Quasicategory X]
    (a : (Δ[1] : SSet.{u}) ⟶ X) (x y : X _⦋0⦌)
    (rx : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.VertexRetraction (SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 2) ≫ a)) x)
    (ry : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.VertexRetraction (SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2) ≫ a)) y) :
    ∃ b : (Δ[1] : SSet.{u}) ⟶ X,
      SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 2) ≫ b) = x ∧
      SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2) ≫ b) = y ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsVertexRetractOf (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex b) := by
  obtain ⟨c, hcx, hcy, hac⟩ := arrow_source_retract_lift a x rx
  have rcy : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.VertexRetraction (SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2) ≫ c)) y := by
    rw [hcy]
    exact ry
  obtain ⟨b, hbc, hby, hcb⟩ := arrow_target_retract_lift c y rcy
  exact ⟨b, (congrArg SSet.yonedaEquiv hbc).trans hcx, hby, hac.trans hcb⟩

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents
