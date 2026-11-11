module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleAugmentationClosedEdge
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleResolvedInfinity
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  (E : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E] (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C (_root_.SerrePositivity.DifferentialGraded.RightModule R E))
/-- 元の同じ実 augmentation の全単体比較。 -/
lemma dgModuleAugmentationSourceLift_down :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationSourceLift R C E F).comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R (RightModule R E)) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationSource R C E F := by
  apply EnrichedFunctor.ext (_root_.SerrePositivity.DifferentialGraded.Complex R) (fun _ => rfl)
  intro X Y
  simp only [EnrichedFunctor.comp_map, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationSourceLift, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp, _root_.SerrePositivity.InfinityCategories.dgObjectImageEvaluation, Category.comp_id, eqToHom_refl]
/-- 元の同じ実 augmentation の全単体比較。 -/
lemma dgModuleAugmentationTargetLift_down :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationTargetLift R C E F).comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R (RightModule R E)) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationTarget R C E F := by
  apply EnrichedFunctor.ext (_root_.SerrePositivity.DifferentialGraded.Complex R) (fun _ => rfl)
  intro X Y
  simp only [EnrichedFunctor.comp_map, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationTargetLift, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp, _root_.SerrePositivity.InfinityCategories.dgObjectImageEvaluation, Category.comp_id, eqToHom_refl]
/-- 元の同じ実 augmentation の全単体比較。 -/
def dgModuleAugmentationUnliftedHomotopy :
    SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationSource R C E F))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationTarget R C E F)) where
  h := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationNerveHomotopy R C E F).h ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R (RightModule R E))
  h₀ := by
    rw [← Category.assoc, (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationNerveHomotopy R C E F).h₀,
      ← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp, dgModuleAugmentationSourceLift_down]
    rfl
  h₁ := by
    rw [← Category.assoc, (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationNerveHomotopy R C E F).h₁,
      ← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp, dgModuleAugmentationTargetLift_down]
    rfl
  rel := by
    ext n s
    exact False.elim s.1.2
/-- 元の同じ実 augmentation の全単体比較。 -/
lemma dgModuleAugmentationUnliftedHomotopy_vertex_edge
    (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E F) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (dgModuleAugmentationUnliftedHomotopy R C E F)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X)).edge = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R (RightModule R E) X.augmentation).edge := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationNerveHomotopy R C E F)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X)).edge.map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R (RightModule R E)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationNerveHomotopy_vertex_edge, ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge_map R (RightModule R E)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R (RightModule R E)) X.augmentation]
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  change (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R (RightModule R E) X.augmentation).edge.toSimplexData.map
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R (RightModule R E))).map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R (RightModule R E))) = _
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.SimplexData.map_comp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp_comp_down, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.SimplexData.map_id]
end SerrePositivity.InfinityCategories.Project.DerivedCategories
