module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Cocone
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoreCoconeLeg
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IdentityCocone

/-!
概要：元の辺を、その終点への退化三角形の余錐として保持する。
方針：最後の頂点を重ねる標準退化を join の座標へ移す。
規約：元の辺を選び直さない。使われ方：局所置換の元の普遍矢印。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

private def edgeTargetShape : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[1] : SSet.{u}) Δ[0] ⟶ Δ[1] :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 1 0).hom ≫ stdSimplex.σ (1 : Fin 2)

private lemma edgeTargetShape_inl :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[1] : SSet.{u}) Δ[0] ≫ edgeTargetShape = 𝟙 Δ[1] := by
  apply SSet.yonedaEquiv.injective
  decide

private lemma edgeTargetShape_inr :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[1] : SSet.{u}) Δ[0] ≫ edgeTargetShape = stdSimplex.δ (0 : Fin 2) := by
  apply SSet.yonedaEquiv.injective
  decide

private lemma edgeTargetShape_source :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.δ (1 : Fin 2)) (𝟙 (Δ[0] : SSet.{u})) ≫ edgeTargetShape =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom := by
  apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv).1
  apply SSet.yonedaEquiv.injective
  decide

private lemma edgeTargetShape_target :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.δ (0 : Fin 2)) (𝟙 (Δ[0] : SSet.{u})) ≫ edgeTargetShape =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom ≫ stdSimplex.σ (0 : Fin 1) ≫
        stdSimplex.δ (0 : Fin 2) := by
  apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv).1
  apply SSet.yonedaEquiv.injective
  decide

/-- 元の辺そのものを、一点の図式からの余錐として読む。 -/
def edgeSourcePointCocone {X : SSet.{u}} (e : (Δ[1] : SSet.{u}) ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (stdSimplex.δ (1 : Fin 2) ≫ e) :=
  ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom ≫ e, by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.joinStdSimplexIso_zero_inl]⟩

/-- 一点余錐の元の脚は、指定した辺そのもの。 -/
lemma edgeSourcePointCocone_leg_edge {X : SSet.{u}} (e : (Δ[1] : SSet.{u}) ⟶ X) :
    ((edgeSourcePointCocone e).leg (𝟙 (Δ[0] : SSet.{u}))).edge = SSet.yonedaEquiv e := by
  change SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) (𝟙 Δ[0]) ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom ≫ e) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_id, Category.id_comp, Iso.inv_hom_id_assoc]

/-- 元の辺からその終点への、最後の辺が恒等である指定余錐。 -/
def edgeTargetCocone {X : SSet.{u}} (e : (Δ[1] : SSet.{u}) ⟶ X) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone e :=
  ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 1 0).hom ≫ stdSimplex.σ (1 : Fin 2) ≫ e, by
    change _ ≫ (edgeTargetShape ≫ e) = e
    rw [← Category.assoc, edgeTargetShape_inl, Category.id_comp]⟩

/-- 指定余錐の頂点は元の辺の終点。 -/
lemma edgeTargetCocone_vertex {X : SSet.{u}} (e : (Δ[1] : SSet.{u}) ⟶ X) :
    (edgeTargetCocone e).vertex = SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2) ≫ e) := by
  change SSet.yonedaEquiv (_ ≫ (edgeTargetShape ≫ e)) = _
  rw [← Category.assoc, edgeTargetShape_inr]

/-- 元の辺の一点余錐の頂点も元の辺の終点。 -/
lemma edgeSourcePointCocone_vertex {X : SSet.{u}} (e : (Δ[1] : SSet.{u}) ⟶ X) :
    (edgeSourcePointCocone e).vertex = SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2) ≫ e) := by
  change SSet.yonedaEquiv (_ ≫ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom ≫ e)) = _
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.joinStdSimplexIso_zero_inr]

/-- 指定余錐の始点側は、元の辺の一点余錐と厳密に一致。 -/
lemma edgeTargetCocone_source {X : SSet.{u}} (e : (Δ[1] : SSet.{u}) ⟶ X) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict e (stdSimplex.δ (1 : Fin 2))).app (Opposite.op ⦋0⦌)
      (edgeTargetCocone e) = edgeSourcePointCocone e := by
  apply Subtype.ext
  change _ ≫ (edgeTargetShape ≫ e) = _
  rw [← Category.assoc, edgeTargetShape_source]
  rfl

/-- 指定余錐の終点側は恒等余錐であり、元の一点図式の余極限。 -/
lemma edgeTargetCocone_target_isColimit {X : SSet.{u}} [Quasicategory X]
    (e : (Δ[1] : SSet.{u}) ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict e (stdSimplex.δ (0 : Fin 2))).app
      (Opposite.op ⦋0⦌) (edgeTargetCocone e)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.isColimitCone_of_point_constant _ (SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2) ≫ e))
  change _ ≫ (edgeTargetShape ≫ e) = _
  rw [← Category.assoc, edgeTargetShape_target, Category.assoc, Category.assoc]
  conv_lhs => rw [← Equiv.symm_apply_apply SSet.yonedaEquiv
      (stdSimplex.δ (0 : Fin 2) ≫ e),
    SSet.yonedaEquiv_symm_zero, SSet.comp_const, SSet.comp_const]

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
