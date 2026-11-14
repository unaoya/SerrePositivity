module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.Nerves.DGModuleAugmentationNervePrism
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Resolutions.DGModuleOutputResolutionInfinity
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering
/-!
概要：厳密切断を通じて、実出力分解の全 ∞ 関手と元の同じ関手を比較する。
方針：対象だけの宇宙持ち上げと二射影の全関手等式から、実 prism を切断に沿って制限する。
規約：全加群の生の nerve への有向ホモトピー。augmentation の可逆性は仮定しない。
使われ方：固定入力の実導来 Hom の全関手比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  (E : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E] (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C (_root_.SerrePositivity.DifferentialGraded.RightModule R E))
/-- 共通対象宇宙にある、元の同じ dg 加群値関手。 -/
def dgModuleOutputOriginalLift :
    DGFunctor R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{v, max (u + 1) w} C)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{max (u + 1) w, v} (RightModule R E)) :=
  ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown R C).comp F).comp
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) w, v} R (RightModule R E))
/-- 対象宇宙を上げた半自由模型から全 dg 加群への実包含。 -/
def dgModuleOutputInclusionLift :
    DGFunctor R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{max (u + 1) w, v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R E))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{max (u + 1) w, v} (RightModule R E)) :=
  ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R E)).comp
    (dgFullSubcategoryInclusion R (RightModule R E) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSemifreeProperty R E))).comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) w, v} R (RightModule R E))
/-- 実半自由出力射影と包含の合成は、同じ augmentation 始点関手。 -/
lemma dgModuleOutputReplacementLift_inclusion :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacementLift R C E F).comp
      (dgModuleOutputInclusionLift.{u, v, w} R E) = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationSourceLift R C E F := by
  apply EnrichedFunctor.ext (_root_.SerrePositivity.DifferentialGraded.Complex R) (fun _ ↦ rfl)
  intro X Y
  simp only [EnrichedFunctor.comp_map, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacementLift,
    dgModuleOutputInclusionLift, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown, _root_.SerrePositivity.InfinityCategories.dgObjectImageEvaluation,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp, dgFullSubcategoryInclusion, Category.comp_id,
    eqToHom_refl]
/-- 実入力射影と元の関手の合成は、同じ augmentation 終点関手。 -/
lemma dgModuleOutputSourceLift_original :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceLift R C E F).comp
      (dgModuleOutputOriginalLift R C E F) = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationTargetLift R C E F := by
  apply EnrichedFunctor.ext (_root_.SerrePositivity.DifferentialGraded.Complex R) (fun _ ↦ rfl)
  intro X Y
  simp only [EnrichedFunctor.comp_map, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceLift,
    dgModuleOutputOriginalLift, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown, _root_.SerrePositivity.InfinityCategories.dgObjectImageEvaluation,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp, Category.comp_id, Category.id_comp, eqToHom_refl]
/-- 厳密切断で戻した終点は、元の同じ全 dg nerve 関手。 -/
lemma dgModuleOutputResolution_original :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceNerveEquivalence R C E F).inv ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationTargetLift R C E F) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgModuleOutputOriginalLift R C E F) := by
  rw [← dgModuleOutputSourceLift_original, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceNerveEquivalence_inv_hom, Category.id_comp]
/-- 厳密切断で戻した始点は、同じ実出力分解 ∞ 関手と包含の合成。 -/
lemma dgModuleOutputResolution_replacement :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceNerveEquivalence R C E F).inv ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationSourceLift R C E F) =
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolutionInfinity R C E F ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgModuleOutputInclusionLift.{u, v, w} R E) := by
  rw [← dgModuleOutputReplacementLift_inclusion, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp]
  rfl
/-- 実出力分解の全 ∞ 関手から元の同じ関手への、実 augmentation のホモトピー。 -/
def dgModuleOutputResolutionHomotopy :
    SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolutionInfinity R C E F ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgModuleOutputInclusionLift.{u, v, w} R E))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgModuleOutputOriginalLift R C E F)) := by
  let H := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationNerveHomotopy R C E F)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceNerveEquivalence R C E F).inv
  exact { h := H.h
          h₀ := H.h₀.trans (dgModuleOutputResolution_replacement R C E F)
          h₁ := H.h₁.trans (dgModuleOutputResolution_original R C E F)
          rel := H.rel }
/-- 元の対象を上げてから実関手を適用すると、元の dg 像の宇宙持ち上げに一致する。 -/
lemma dgModuleOutputOriginalLift_up :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, v, max (u + 1) w} R C).comp
      (dgModuleOutputOriginalLift R C E F) =
        F.comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) w, v} R (RightModule R E)) := by
  apply EnrichedFunctor.ext (_root_.SerrePositivity.DifferentialGraded.Complex R) (fun _ ↦ rfl)
  intro X Y
  simp only [EnrichedFunctor.comp_map, dgModuleOutputOriginalLift,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown, _root_.SerrePositivity.InfinityCategories.dgObjectImageEvaluation, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp,
    Category.comp_id, Category.id_comp, eqToHom_refl]
end SerrePositivity.InfinityCategories.Project.DerivedCategories
