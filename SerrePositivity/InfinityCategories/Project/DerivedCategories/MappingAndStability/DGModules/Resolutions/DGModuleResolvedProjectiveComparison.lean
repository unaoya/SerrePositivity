module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Bar.DGModuleAugmentationProjectiveIso
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Resolutions.DGModuleResolvedInfinity
/-!
概要：射影的出力の実分解関手を、元の同じ dg 関手の包含像へ全関手同型で比較する。
方針：同じ augmentation 同型を前後合成し、対象宇宙の上げ下げを厳密に照合する。
規約：比較は元の全単体上の同型。使われ方：一般双加群作用の graph 比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  (E : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E] (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C (_root_.SerrePositivity.DifferentialGraded.RightModule R E))
/-- 持ち上げた包含を下げると、同じ半自由包含の合成と厳密に一致する。 -/
lemma dgModuleOutputInclusionLift_down :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputInclusionLift.{u, max (u + 1) v, v} R E).comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown R (RightModule R E)) =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R E)).comp
      (dgFullSubcategoryInclusion R (RightModule R E) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSemifreeProperty R E)) := by
  apply EnrichedFunctor.ext (_root_.SerrePositivity.DifferentialGraded.Complex R) (fun _ => rfl)
  intro X Y
  simp only [EnrichedFunctor.comp_map, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputInclusionLift, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown,
    _root_.SerrePositivity.InfinityCategories.dgObjectImageEvaluation, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp, dgFullSubcategoryInclusion,
    Category.comp_id, eqToHom_refl]
/-- 元の関手を前後で上げ下げすると、元の同じ dg 関手へ戻る。 -/
lemma dgModuleOutputOriginalLift_up_down :
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C).comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputOriginalLift R C E F)).comp
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown R (RightModule R E)) = F := by
  apply EnrichedFunctor.ext (_root_.SerrePositivity.DifferentialGraded.Complex R) (fun _ => rfl)
  intro X Y
  simp only [EnrichedFunctor.comp_map, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputOriginalLift, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown,
    _root_.SerrePositivity.InfinityCategories.dgObjectImageEvaluation, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp,
    Category.comp_id, Category.id_comp, eqToHom_refl]
/-- 射影的出力の場合、実半自由分解関手の包含は元の同じ dg 関手と同型。 -/
def dgModuleResolvedInfinity_inclusionIso
    (hF : ∀ x, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleProjectiveProperty R E (F.obj x)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R C E F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
      (dgFullSubcategoryInclusion R (RightModule R E) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSemifreeProperty R E)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F) := by
  have e := ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolutionProjectiveIso R C E F hF).precomp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C))).postcomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R
        (_root_.SerrePositivity.DifferentialGraded.RightModule R E)))
  have h1 := congrArg (fun H => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map H) (dgModuleOutputInclusionLift_down R E)
  have h2 := congrArg (fun H => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map H) (dgModuleOutputOriginalLift_up_down R C E F)
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp, Category.assoc] at h1 h2
  simp only [Category.assoc] at e
  rw [h1, h2] at e
  exact e
end SerrePositivity.InfinityCategories.Project.DerivedCategories
