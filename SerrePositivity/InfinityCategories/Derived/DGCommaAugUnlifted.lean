module
public import SerrePositivity.InfinityCategories.Derived.DGCommaAugClosedEdge
/-!
概要：実commaの augmentation を元の元の dg 圏 nerve 上の同じホモトピーへ戻す。
方針：対象宇宙の上げ下げを相殺し、元の閉辺を全一次単体として回収する。
規約：augmentation の終点に射影性を課さない。使われ方：射影的 Hom 試験の全関手比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (C E : Type (max (u + 1) v))
  [DGCategory R C] [DGCategory R E] (F : DGFunctor R C E)
/-- 元の同じ実 augmentation の全単体比較。 -/
lemma dgCommaAugmentationSourceLift_down :
    (dgCommaAugmentationSourceLift R C E F).comp
      (dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R E) =
      dgCommaAugmentationSource R C E F := by
  apply EnrichedFunctor.ext (Complex R) (fun _ => rfl)
  intro X Y
  simp only [EnrichedFunctor.comp_map, dgCommaAugmentationSourceLift, dgUniverseLiftDown,
    dgUniverseLiftUp, dgObjectImageEvaluation, Category.comp_id, eqToHom_refl]
/-- 元の同じ実 augmentation の全単体比較。 -/
lemma dgCommaAugmentationTargetLift_down :
    (dgCommaAugmentationTargetLift R C E F).comp
      (dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R E) =
      dgCommaAugmentationTarget R C E F := by
  apply EnrichedFunctor.ext (Complex R) (fun _ => rfl)
  intro X Y
  simp only [EnrichedFunctor.comp_map, dgCommaAugmentationTargetLift, dgUniverseLiftDown,
    dgUniverseLiftUp, dgObjectImageEvaluation, Category.comp_id, eqToHom_refl]
/-- 元の同じ実 augmentation の全単体比較。 -/
def dgCommaAugmentationUnliftedHomotopy :
    SSet.Homotopy (dgNerve.map (dgCommaAugmentationSource R C E F))
      (dgNerve.map (dgCommaAugmentationTarget R C E F)) where
  h := (dgCommaAugmentationNerveHomotopy R C E F).h ≫
    dgNerve.map (dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R E)
  h₀ := by
    rw [← Category.assoc, (dgCommaAugmentationNerveHomotopy R C E F).h₀,
      ← dgNerve.map_comp, dgCommaAugmentationSourceLift_down]
    rfl
  h₁ := by
    rw [← Category.assoc, (dgCommaAugmentationNerveHomotopy R C E F).h₁,
      ← dgNerve.map_comp, dgCommaAugmentationTargetLift_down]
    rfl
  rel := by
    ext n s
    exact False.elim s.1.2
/-- 元の同じ実 augmentation の全単体比較。 -/
lemma dgCommaAugmentationUnliftedHomotopy_vertex_edge
    (X : DGFunctorCommaObject R C E F) :
    (simplicialHomotopyVertexEdge (dgCommaAugmentationUnliftedHomotopy R C E F)
      (Simplex.vertex X)).edge = (dgClosedEdge R E X.augmentation).edge := by
  change (simplicialHomotopyVertexEdge (dgCommaAugmentationNerveHomotopy R C E F)
    (Simplex.vertex X)).edge.map
      (dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R E) = _
  rw [dgCommaAugmentationNerveHomotopy_vertex_edge, ← dgClosedEdge_map R E
    (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R E) X.augmentation]
  apply Simplex.ext
  change (((dgClosedEdge R E X.augmentation).edge.toSimplexData.map
    (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R E)).map
      (dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R E)) = _
  rw [← SimplexData.map_comp, dgUniverseLiftUp_comp_down, SimplexData.map_id]
end SerrePositivity.InfinityCategories
