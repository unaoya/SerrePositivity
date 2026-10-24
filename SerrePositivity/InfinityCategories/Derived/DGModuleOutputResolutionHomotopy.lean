module
public import SerrePositivity.InfinityCategories.Derived.DGModuleAugmentationNervePrism
public import SerrePositivity.InfinityCategories.Derived.DGModuleOutputResolutionInfinity
public import SerrePositivity.InfinityCategories.F1B.Homotopy.HomotopyWhiskering
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] [Small.{u} E] (F : DGFunctor R C (RightModule R E))
/-- 共通対象宇宙にある、元の同じ dg 加群値関手。 -/
def dgModuleOutputOriginalLift :
    DGFunctor R (DGUniverseLift.{v, max (u + 1) w} C)
      (DGUniverseLift.{max (u + 1) w, v} (RightModule R E)) :=
  ((dgUniverseLiftDown R C).comp F).comp
    (dgUniverseLiftUp.{u, max (u + 1) w, v} R (RightModule R E))
/-- 対象宇宙を上げた半自由模型から全 dg 加群への実包含。 -/
def dgModuleOutputInclusionLift :
    DGFunctor R (DGUniverseLift.{max (u + 1) w, v} (SemifreeDGModules R E))
      (DGUniverseLift.{max (u + 1) w, v} (RightModule R E)) :=
  ((dgUniverseLiftDown R (SemifreeDGModules R E)).comp
    (dgFullSubcategoryInclusion R (RightModule R E) (dgModuleSemifreeProperty R E))).comp
      (dgUniverseLiftUp.{u, max (u + 1) w, v} R (RightModule R E))
/-- 実半自由出力射影と包含の合成は、同じ augmentation 始点関手。 -/
lemma dgModuleOutputReplacementLift_inclusion :
    (dgModuleFunctorResolutionReplacementLift R C E F).comp
      (dgModuleOutputInclusionLift.{u, v, w} R E) = dgModuleAugmentationSourceLift R C E F := by
  apply EnrichedFunctor.ext (Complex R) (fun _ ↦ rfl)
  intro X Y
  simp only [EnrichedFunctor.comp_map, dgModuleFunctorResolutionReplacementLift,
    dgModuleOutputInclusionLift, dgUniverseLiftDown, dgObjectImageEvaluation,
    dgUniverseLiftUp, dgFullSubcategoryInclusion, Category.comp_id,
    eqToHom_refl]
/-- 実入力射影と元の関手の合成は、同じ augmentation 終点関手。 -/
lemma dgModuleOutputSourceLift_original :
    (dgModuleFunctorResolutionSourceLift R C E F).comp
      (dgModuleOutputOriginalLift R C E F) = dgModuleAugmentationTargetLift R C E F := by
  apply EnrichedFunctor.ext (Complex R) (fun _ ↦ rfl)
  intro X Y
  simp only [EnrichedFunctor.comp_map, dgModuleFunctorResolutionSourceLift,
    dgModuleOutputOriginalLift, dgUniverseLiftDown, dgObjectImageEvaluation,
    dgUniverseLiftUp, Category.comp_id, Category.id_comp, eqToHom_refl]
/-- 厳密切断で戻した終点は、元の同じ全 dg nerve 関手。 -/
lemma dgModuleOutputResolution_original :
    (dgModuleFunctorResolutionSourceNerveEquivalence R C E F).inv ≫
      dgNerve.map (dgModuleAugmentationTargetLift R C E F) =
        dgNerve.map (dgModuleOutputOriginalLift R C E F) := by
  rw [← dgModuleOutputSourceLift_original, dgNerve.map_comp, ← Category.assoc,
    dgModuleFunctorResolutionSourceNerveEquivalence_inv_hom, Category.id_comp]
/-- 厳密切断で戻した始点は、同じ実出力分解 ∞ 関手と包含の合成。 -/
lemma dgModuleOutputResolution_replacement :
    (dgModuleFunctorResolutionSourceNerveEquivalence R C E F).inv ≫
      dgNerve.map (dgModuleAugmentationSourceLift R C E F) =
        dgModuleOutputResolutionInfinity R C E F ≫
          dgNerve.map (dgModuleOutputInclusionLift.{u, v, w} R E) := by
  rw [← dgModuleOutputReplacementLift_inclusion, dgNerve.map_comp]
  rfl
/-- 実出力分解の全 ∞ 関手から元の同じ関手への、実 augmentation のホモトピー。 -/
def dgModuleOutputResolutionHomotopy :
    SSet.Homotopy (dgModuleOutputResolutionInfinity R C E F ≫
      dgNerve.map (dgModuleOutputInclusionLift.{u, v, w} R E))
      (dgNerve.map (dgModuleOutputOriginalLift R C E F)) := by
  let H := functorHomotopyPrecomp (dgModuleAugmentationNerveHomotopy R C E F)
    (dgModuleFunctorResolutionSourceNerveEquivalence R C E F).inv
  exact { h := H.h
          h₀ := H.h₀.trans (dgModuleOutputResolution_replacement R C E F)
          h₁ := H.h₁.trans (dgModuleOutputResolution_original R C E F)
          rel := H.rel }
/-- 元の対象を上げてから実関手を適用すると、元の dg 像の宇宙持ち上げに一致する。 -/
lemma dgModuleOutputOriginalLift_up :
    (dgUniverseLiftUp.{u, v, max (u + 1) w} R C).comp
      (dgModuleOutputOriginalLift R C E F) =
        F.comp (dgUniverseLiftUp.{u, max (u + 1) w, v} R (RightModule R E)) := by
  apply EnrichedFunctor.ext (Complex R) (fun _ ↦ rfl)
  intro X Y
  simp only [EnrichedFunctor.comp_map, dgModuleOutputOriginalLift,
    dgUniverseLiftDown, dgObjectImageEvaluation, dgUniverseLiftUp,
    Category.comp_id, Category.id_comp, eqToHom_refl]
end SerrePositivity.InfinityCategories
