module
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolutionPrecompFunctor
public import SerrePositivity.InfinityCategories.Derived.DGModuleOutputResolutionInfinity
/-!
概要：前合成の同じ実分解 dg 関手は、宇宙持ち上げ後の両射影を厳密に保つ。
方針：同じ全 Hom・実二射影・比較 cochain の等式を保持して構成する。
規約：元の出力の射影性と入力の小ささは不要。使われ方：二変数 Hom の固定入力制限の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve MonoidalCategory
open CochainComplex HomComplex SSet
variable (R : Type u) [CommRing R] (A C : Type v) [DGCategory R A] [DGCategory R C]
  (E : Type w) [DGCategory R E] [Small.{u} E]
  (H : DGFunctor R A C) (F : DGFunctor R C (RightModule R E))
/-- 対象宇宙を持ち上げた同じ入力射影との厳密な前合成等式。 -/
lemma dgModuleResolutionPrecompFunctor_sourceLift :
    (dgModuleResolutionPrecompFunctor R A C E H F).comp
      (dgModuleFunctorResolutionSourceLift R C E F) =
    (dgModuleFunctorResolutionSourceLift R A E (H.comp F)).comp
      ((dgUniverseLiftDown.{u, v, max (u + 1) w} R A).comp
        (H.comp (dgUniverseLiftUp.{u, v, max (u + 1) w} R C))) := by
  apply EnrichedFunctor.ext (Complex R)
    (F := (dgModuleResolutionPrecompFunctor R A C E H F).comp
      (dgModuleFunctorResolutionSourceLift R C E F))
    (G := (dgModuleFunctorResolutionSourceLift R A E (H.comp F)).comp
      ((dgUniverseLiftDown.{u, v, max (u + 1) w} R A).comp
        (H.comp (dgUniverseLiftUp.{u, v, max (u + 1) w} R C)))) (fun _ => rfl)
  intro X Y
  simp only [EnrichedFunctor.comp_map, dgModuleResolutionPrecompFunctor,
    dgModuleFunctorResolutionSourceLift, dgModuleFunctorResolutionSource,
    dgUniverseLiftUp, dgUniverseLiftDown, dgObjectImageEvaluation,
    eqToHom_refl, Category.comp_id, Category.id_comp]
  exact dgModuleResolutionPrecompHom_source R A C E H F X Y
/-- 対象宇宙を持ち上げた同じ半自由出力射影も厳密に保つ。 -/
lemma dgModuleResolutionPrecompFunctor_replacementLift :
    (dgModuleResolutionPrecompFunctor R A C E H F).comp
      (dgModuleFunctorResolutionReplacementLift R C E F) =
    dgModuleFunctorResolutionReplacementLift R A E (H.comp F) := by
  apply EnrichedFunctor.ext (Complex R)
    (F := (dgModuleResolutionPrecompFunctor R A C E H F).comp
      (dgModuleFunctorResolutionReplacementLift R C E F))
    (G := dgModuleFunctorResolutionReplacementLift R A E (H.comp F)) (fun _ => rfl)
  intro X Y
  simp only [EnrichedFunctor.comp_map, dgModuleResolutionPrecompFunctor,
    dgModuleFunctorResolutionReplacementLift, dgModuleFunctorResolutionReplacement,
    dgUniverseLiftUp, eqToHom_refl, Category.comp_id]
  exact dgModuleResolutionPrecompHom_replacement R A C E H F X Y
end SerrePositivity.InfinityCategories
