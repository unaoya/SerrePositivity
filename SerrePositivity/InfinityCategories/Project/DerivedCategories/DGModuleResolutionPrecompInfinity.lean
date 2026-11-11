module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleResolutionPrecompFunctor
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleOutputResolutionInfinity
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded MonoidalCategory
open CochainComplex HomComplex SSet
variable (R : Type u) [CommRing R] (A C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R A] [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  (E : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
  (H : _root_.SerrePositivity.DifferentialGraded.DGFunctor R A C) (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C (_root_.SerrePositivity.DifferentialGraded.RightModule R E))
/-- 対象宇宙を持ち上げた同じ入力射影との厳密な前合成等式。 -/
lemma dgModuleResolutionPrecompFunctor_sourceLift :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompFunctor R A C E H F).comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceLift R C E F) =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceLift R A E (H.comp F)).comp
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, v, max (u + 1) w} R A).comp
        (H.comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, v, max (u + 1) w} R C))) := by
  apply EnrichedFunctor.ext (_root_.SerrePositivity.DifferentialGraded.Complex R)
    (F := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompFunctor R A C E H F).comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceLift R C E F))
    (G := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceLift R A E (H.comp F)).comp
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, v, max (u + 1) w} R A).comp
        (H.comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, v, max (u + 1) w} R C)))) (fun _ => rfl)
  intro X Y
  simp only [EnrichedFunctor.comp_map, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompFunctor,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceLift, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSource,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown, _root_.SerrePositivity.InfinityCategories.dgObjectImageEvaluation,
    eqToHom_refl, Category.comp_id, Category.id_comp]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompHom_source R A C E H F X Y
/-- 対象宇宙を持ち上げた同じ半自由出力射影も厳密に保つ。 -/
lemma dgModuleResolutionPrecompFunctor_replacementLift :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompFunctor R A C E H F).comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacementLift R C E F) =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacementLift R A E (H.comp F) := by
  apply EnrichedFunctor.ext (_root_.SerrePositivity.DifferentialGraded.Complex R)
    (F := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompFunctor R A C E H F).comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacementLift R C E F))
    (G := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacementLift R A E (H.comp F)) (fun _ => rfl)
  intro X Y
  simp only [EnrichedFunctor.comp_map, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompFunctor,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacementLift, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacement,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp, eqToHom_refl, Category.comp_id]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompHom_replacement R A C E H F X Y
end SerrePositivity.InfinityCategories.Project.DerivedCategories
