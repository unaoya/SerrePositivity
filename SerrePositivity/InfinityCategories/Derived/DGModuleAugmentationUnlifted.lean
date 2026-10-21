module
public import SerrePositivity.InfinityCategories.Derived.DGModuleAugmentationClosedEdge
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedInfinity
/-!
概要：実出力分解の augmentation を元の全加群 nerve 上の同じホモトピーへ戻す。
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
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [DGCategory R C]
  (E : Type v) [DGCategory R E] [Small.{u} E] (F : DGFunctor R C (RightModule R E))
/-- 元の同じ実 augmentation の全単体比較。 -/
lemma dgModuleAugmentationSourceLift_down :
    (dgModuleAugmentationSourceLift R C E F).comp
      (dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R (RightModule R E)) =
      dgModuleAugmentationSource R C E F := by
  apply EnrichedFunctor.ext (Complex R) (fun _ => rfl)
  intro X Y
  simp only [EnrichedFunctor.comp_map, dgModuleAugmentationSourceLift, dgUniverseLiftDown,
    dgUniverseLiftUp, dgObjectImageEvaluation, Category.comp_id, eqToHom_refl]
/-- 元の同じ実 augmentation の全単体比較。 -/
lemma dgModuleAugmentationTargetLift_down :
    (dgModuleAugmentationTargetLift R C E F).comp
      (dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R (RightModule R E)) =
      dgModuleAugmentationTarget R C E F := by
  apply EnrichedFunctor.ext (Complex R) (fun _ => rfl)
  intro X Y
  simp only [EnrichedFunctor.comp_map, dgModuleAugmentationTargetLift, dgUniverseLiftDown,
    dgUniverseLiftUp, dgObjectImageEvaluation, Category.comp_id, eqToHom_refl]
/-- 元の同じ実 augmentation の全単体比較。 -/
def dgModuleAugmentationUnliftedHomotopy :
    SSet.Homotopy (dgNerve.map (dgModuleAugmentationSource R C E F))
      (dgNerve.map (dgModuleAugmentationTarget R C E F)) where
  h := (dgModuleAugmentationNerveHomotopy R C E F).h ≫
    dgNerve.map (dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R (RightModule R E))
  h₀ := by
    rw [← Category.assoc, (dgModuleAugmentationNerveHomotopy R C E F).h₀,
      ← dgNerve.map_comp, dgModuleAugmentationSourceLift_down]
    rfl
  h₁ := by
    rw [← Category.assoc, (dgModuleAugmentationNerveHomotopy R C E F).h₁,
      ← dgNerve.map_comp, dgModuleAugmentationTargetLift_down]
    rfl
  rel := by
    ext n s
    exact False.elim s.1.2
/-- 元の同じ実 augmentation の全単体比較。 -/
lemma dgModuleAugmentationUnliftedHomotopy_vertex_edge
    (X : DGModuleFunctorResolutionObject R C E F) :
    (simplicialHomotopyVertexEdge (dgModuleAugmentationUnliftedHomotopy R C E F)
      (Simplex.vertex X)).edge = (dgClosedEdge R (RightModule R E) X.augmentation).edge := by
  change (simplicialHomotopyVertexEdge (dgModuleAugmentationNerveHomotopy R C E F)
    (Simplex.vertex X)).edge.map
      (dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R (RightModule R E)) = _
  rw [dgModuleAugmentationNerveHomotopy_vertex_edge, ← dgClosedEdge_map R (RightModule R E)
    (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R (RightModule R E)) X.augmentation]
  apply Simplex.ext
  change (((dgClosedEdge R (RightModule R E) X.augmentation).edge.toSimplexData.map
    (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R (RightModule R E))).map
      (dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R (RightModule R E))) = _
  rw [← SimplexData.map_comp, dgUniverseLiftUp_comp_down, SimplexData.map_id]
end SerrePositivity.InfinityCategories
