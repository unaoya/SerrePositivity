module
public import SerrePositivity.InfinityCategories.Derived.DGModuleAugmentationProjectiveIso
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedInfinity
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [DGCategory R C]
  (E : Type v) [DGCategory R E] [Small.{u} E] (F : DGFunctor R C (RightModule R E))
/-- 持ち上げた包含を下げると、同じ半自由包含の合成と厳密に一致する。 -/
lemma dgModuleOutputInclusionLift_down :
    (dgModuleOutputInclusionLift.{u, max (u + 1) v, v} R E).comp
      (dgUniverseLiftDown R (RightModule R E)) =
    (dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R (SemifreeDGModules R E)).comp
      (dgFullSubcategoryInclusion R (RightModule R E) (dgModuleSemifreeProperty R E)) := by
  apply EnrichedFunctor.ext (Complex R) (fun _ => rfl)
  intro X Y
  simp only [EnrichedFunctor.comp_map, dgModuleOutputInclusionLift, dgUniverseLiftDown,
    dgObjectImageEvaluation, dgUniverseLiftUp, dgFullSubcategoryInclusion,
    Category.comp_id, eqToHom_refl]
/-- 元の関手を前後で上げ下げすると、元の同じ dg 関手へ戻る。 -/
lemma dgModuleOutputOriginalLift_up_down :
    ((dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C).comp
      (dgModuleOutputOriginalLift R C E F)).comp
        (dgUniverseLiftDown R (RightModule R E)) = F := by
  apply EnrichedFunctor.ext (Complex R) (fun _ => rfl)
  intro X Y
  simp only [EnrichedFunctor.comp_map, dgModuleOutputOriginalLift, dgUniverseLiftDown,
    dgObjectImageEvaluation, dgUniverseLiftUp,
    Category.comp_id, Category.id_comp, eqToHom_refl]
/-- 射影的出力の場合、実半自由分解関手の包含は元の同じ dg 関手と同型。 -/
def dgModuleResolvedInfinity_inclusionIso
    (hF : ∀ x, dgModuleProjectiveProperty R E (F.obj x)) :
    FunctorIso (dgModuleResolvedInfinity R C E F ≫ dgNerve.map
      (dgFullSubcategoryInclusion R (RightModule R E) (dgModuleSemifreeProperty R E)))
      (dgNerve.map F) := by
  have e := ((dgModuleOutputResolutionProjectiveIso R C E F hF).precomp
    (dgNerve.map (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C))).postcomp
      (dgNerve.map (dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R
        (RightModule R E)))
  have h1 := congrArg (fun H => dgNerve.map H) (dgModuleOutputInclusionLift_down R E)
  have h2 := congrArg (fun H => dgNerve.map H) (dgModuleOutputOriginalLift_up_down R C E F)
  simp only [dgNerve.map_comp, Category.assoc] at h1 h2
  simp only [Category.assoc] at e
  rw [h1, h2] at e
  exact e
end SerrePositivity.InfinityCategories
