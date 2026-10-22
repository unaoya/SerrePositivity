module

public import SerrePositivity.InfinityCategories.Stable.SliceSquareDiagram
public import SerrePositivity.InfinityCategories.Stable.CosliceCoconeDiagramEvaluation
public import SerrePositivity.InfinityCategories.Core.TerminalUniqueness

/-!
概要：一点上の slice・coslice の全族を、元の辺の関手 ∞ 圏へ写す。
方針：全錐・全余錐の族の比較を、元の零単体どうしの join の同型で制限する。
規約：元の辺そのものと両端点を厳密に回収する。
使われ方：辺の関手 ∞ 圏内の retract を両端点の retract から構成する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 一点上の元の slice の全錐の族を、元の辺の関手 ∞ 圏へ写す。 -/
def pointSliceArrowMap {X : SSet.{u}} (p : (Δ[0] : SSet.{u}) ⟶ X) :
    sliceOver p ⟶ (ihom (Δ[1] : SSet.{u})).obj X :=
  sliceConeDiagramMap p ≫ (pre (joinStdSimplexIso 0 0).inv).app X

/-- 元の slice の全辺表示の零次成分は、同じ全錐の元の辺。 -/
lemma pointSliceArrowMap_vertex {X : SSet.{u}} (p : (Δ[0] : SSet.{u}) ⟶ X)
    (c : JoinCone p) : (pointSliceArrowMap p).app (Opposite.op ⦋0⦌) c =
      functorVertex ((joinStdSimplexIso 0 0).inv ≫ c.val) := by
  change ((pre (joinStdSimplexIso 0 0).inv).app X).app (Opposite.op ⦋0⦌)
    ((sliceConeDiagramMap p).app (Opposite.op ⦋0⦌) c) = _
  rw [sliceConeDiagramMap_vertex]
  rfl

/-- 一点下の元の coslice の全余錐の族を、元の辺の関手 ∞ 圏へ写す。 -/
def pointCosliceArrowMap {X : SSet.{u}} (p : (Δ[0] : SSet.{u}) ⟶ X) :
    sliceUnder p ⟶ (ihom (Δ[1] : SSet.{u})).obj X :=
  cosliceCoconeDiagramMap p ≫ (pre (joinStdSimplexIso 0 0).inv).app X

/-- 元の coslice の全辺表示の零次成分は、同じ全余錐の元の辺。 -/
lemma pointCosliceArrowMap_vertex {X : SSet.{u}} (p : (Δ[0] : SSet.{u}) ⟶ X)
    (c : JoinCocone p) : (pointCosliceArrowMap p).app (Opposite.op ⦋0⦌) c =
      functorVertex ((joinStdSimplexIso 0 0).inv ≫ c.val) := by
  change ((pre (joinStdSimplexIso 0 0).inv).app X).app (Opposite.op ⦋0⦌)
    ((cosliceCoconeDiagramMap p).app (Opposite.op ⦋0⦌) c) = _
  rw [cosliceCoconeDiagramMap_vertex]
  rfl

/-- 元の一点上の錐の辺表示の始点は、同じ錐の頂点そのもの。 -/
lemma pointSliceArrow_source {X : SSet.{u}} {p : (Δ[0] : SSet.{u}) ⟶ X}
    (c : JoinCone p) : stdSimplex.δ (1 : Fin 2) ≫
      (joinStdSimplexIso 0 0).inv ≫ c.val = SSet.yonedaEquiv.symm c.vertex := by
  rw [← joinStdSimplexIso_zero_inl, Category.assoc, Iso.hom_inv_id_assoc]
  exact (SSet.yonedaEquiv.symm_apply_apply _).symm

/-- 元の一点上の錐の辺表示の終点は、固定した同じ図式。 -/
lemma pointSliceArrow_target {X : SSet.{u}} {p : (Δ[0] : SSet.{u}) ⟶ X}
    (c : JoinCone p) : stdSimplex.δ (0 : Fin 2) ≫
      (joinStdSimplexIso 0 0).inv ≫ c.val = p := by
  rw [← joinStdSimplexIso_zero_inr, Category.assoc, Iso.hom_inv_id_assoc]
  exact c.property

/-- 元の一点下の余錐の辺表示の始点は、固定した同じ図式。 -/
lemma pointCosliceArrow_source {X : SSet.{u}} {p : (Δ[0] : SSet.{u}) ⟶ X}
    (c : JoinCocone p) : stdSimplex.δ (1 : Fin 2) ≫
      (joinStdSimplexIso 0 0).inv ≫ c.val = p := by
  rw [← joinStdSimplexIso_zero_inl, Category.assoc, Iso.hom_inv_id_assoc]
  exact c.property

/-- 元の一点下の余錐の辺表示の終点は、同じ余錐の頂点そのもの。 -/
lemma pointCosliceArrow_target {X : SSet.{u}} {p : (Δ[0] : SSet.{u}) ⟶ X}
    (c : JoinCocone p) : stdSimplex.δ (0 : Fin 2) ≫
      (joinStdSimplexIso 0 0).inv ≫ c.val = SSet.yonedaEquiv.symm c.vertex := by
  rw [← joinStdSimplexIso_zero_inr, Category.assoc, Iso.hom_inv_id_assoc]
  exact (SSet.yonedaEquiv.symm_apply_apply _).symm

/-- 元の辺を、その同じ終点上の全錐として表す。 -/
def arrowPointCone {X : SSet.{u}} (a : (Δ[1] : SSet.{u}) ⟶ X) :
    JoinCone (stdSimplex.δ (0 : Fin 2) ≫ a) :=
  ⟨(joinStdSimplexIso 0 0).hom ≫ a, by
    rw [← Category.assoc, joinStdSimplexIso_zero_inr]⟩

/-- 元の辺を、その同じ始点下の全余錐として表す。 -/
def arrowPointCocone {X : SSet.{u}} (a : (Δ[1] : SSet.{u}) ⟶ X) :
    JoinCocone (stdSimplex.δ (1 : Fin 2) ≫ a) :=
  ⟨(joinStdSimplexIso 0 0).hom ≫ a, by
    rw [← Category.assoc, joinStdSimplexIso_zero_inl]⟩

/-- 元の辺の全錐表示から、同じ辺の関手頂点を厳密に回収する。 -/
lemma pointSliceArrowMap_arrowPointCone {X : SSet.{u}} (a : (Δ[1] : SSet.{u}) ⟶ X) :
    (pointSliceArrowMap (stdSimplex.δ (0 : Fin 2) ≫ a)).app (Opposite.op ⦋0⦌)
      (arrowPointCone a) = functorVertex a := by
  rw [pointSliceArrowMap_vertex]
  change functorVertex ((joinStdSimplexIso 0 0).inv ≫ ((joinStdSimplexIso 0 0).hom ≫ a)) = _
  rw [Iso.inv_hom_id_assoc]

/-- 元の辺の全余錐表示から、同じ辺の関手頂点を厳密に回収する。 -/
lemma pointCosliceArrowMap_arrowPointCocone {X : SSet.{u}} (a : (Δ[1] : SSet.{u}) ⟶ X) :
    (pointCosliceArrowMap (stdSimplex.δ (1 : Fin 2) ≫ a)).app (Opposite.op ⦋0⦌)
      (arrowPointCocone a) = functorVertex a := by
  rw [pointCosliceArrowMap_vertex]
  change functorVertex ((joinStdSimplexIso 0 0).inv ≫ ((joinStdSimplexIso 0 0).hom ≫ a)) = _
  rw [Iso.inv_hom_id_assoc]

end SerrePositivity.InfinityCategories.F2.Idempotent
