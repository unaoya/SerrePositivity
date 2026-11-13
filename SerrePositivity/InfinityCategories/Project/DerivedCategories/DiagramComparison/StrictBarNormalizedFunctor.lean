module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictBarNormalizedThetaNaturality
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SmallStrictBarNormalizedComparison

/-!
概要：同じ正規化coherent barを元のstrict図式の関手にし、元の正規化射影を自然変換にする。
方針：証明したMC可換式で元のgraded射を微分変更後へ移し、全次数の評価で関手則を確認する。
規約：正規化射影・補正包含は既存のものを保持する。
使われ方：3b-3 R6、同じ正規化比較と指定余錐の全パラメーター比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite SSet
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
open SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract
open SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison

variable (A : Type u) [CommRing A] (J : Type) [SmallCategory J]

/-- 元のgraded射を、同じ正規化MC微分の間の実鎖写像にする。 -/
def strictBarNormalizedMap {F G : J ⥤ ModuleCategory A PUnit.{1}} (η : F ⟶ G) :
    ForgetEnrichment.of (Complex A)
        (dgCoherentBarNormalizedModuleUnconditional A PUnit.{1} (smallStrictBarDiagram A F)) ⟶
      ForgetEnrichment.of (Complex A)
        (dgCoherentBarNormalizedModuleUnconditional A PUnit.{1} (smallStrictBarDiagram A G)) :=
  dgBarMaurerCartanModuleMap A PUnit.{1}
    (dgCoherentBarNormalizedTheta A PUnit.{1} (smallStrictBarDiagram A F))
    (dgCoherentBarNormalizedTheta A PUnit.{1} (smallStrictBarDiagram A G))
    (dgCoherentBarNormalizedTheta_maurerCartan A PUnit.{1} (smallStrictBarDiagram A F)
      (dgCoherentBarMaurerCartan_unconditional A PUnit.{1} (smallStrictBarDiagram A F)))
    (dgCoherentBarNormalizedTheta_maurerCartan A PUnit.{1} (smallStrictBarDiagram A G)
      (dgCoherentBarMaurerCartan_unconditional A PUnit.{1} (smallStrictBarDiagram A G)))
    (strictBarNormalizedGradedMap A J η) (strictBarNormalizedTheta_naturality A J η)

/-- 同じ正規化barの射も、各内部次数では元のgraded射である。 -/
lemma strictBarNormalizedMap_component {F G : J ⥤ ModuleCategory A PUnit.{1}}
    (η : F ⟶ G) (q : ℤ) :
    ((moduleEvaluation A PUnit.{1} PUnit.unit).map (strictBarNormalizedMap A J η)).f q =
      ((moduleEvaluation A PUnit.{1} PUnit.unit).map (strictBarNormalizedGradedMap A J η)).f q := by
  exact dgBarMaurerCartanModuleMap_eval_f _ _ _ _ _ _ _ _ _ _

/-- 元のstrict図式と自然変換に対する、同じ正規化coherent barの通常関手。 -/
def strictBarNormalizedFunctor : (J ⥤ ModuleCategory A PUnit.{1}) ⥤ ModuleCategory A PUnit.{1} where
  obj F := ForgetEnrichment.of (Complex A)
    (dgCoherentBarNormalizedModuleUnconditional A PUnit.{1} (smallStrictBarDiagram A F))
  map η := strictBarNormalizedMap A J η
  map_id F := by
    apply (moduleEvaluation A PUnit.{1} PUnit.unit).map_injective
    apply HomologicalComplex.Hom.ext
    funext q
    rw [strictBarNormalizedMap_component, (moduleEvaluation A PUnit.{1} PUnit.unit).map_id]
    have h := congrArg (fun f => ((moduleEvaluation A PUnit.{1} PUnit.unit).map f).f q)
      ((strictBarNormalizedGradedFunctor A J).map_id F)
    change ((moduleEvaluation A PUnit.{1} PUnit.unit).map
      (strictBarNormalizedGradedMap A J (𝟙 F))).f q =
        ((moduleEvaluation A PUnit.{1} PUnit.unit).map
          (𝟙 (dgCoherentBarNormalizedGraded A PUnit.{1} (smallStrictBarDiagram A F)))).f q at h
    simpa only [CategoryTheory.Functor.map_id, HomologicalComplex.id_f] using! h
  map_comp η θ := by
    apply (moduleEvaluation A PUnit.{1} PUnit.unit).map_injective
    apply HomologicalComplex.Hom.ext
    funext q
    rw [(moduleEvaluation A PUnit.{1} PUnit.unit).map_comp, HomologicalComplex.comp_f,
      strictBarNormalizedMap_component, strictBarNormalizedMap_component,
      strictBarNormalizedMap_component]
    have h := congrArg (fun f => ((moduleEvaluation A PUnit.{1} PUnit.unit).map f).f q)
      ((strictBarNormalizedGradedFunctor A J).map_comp η θ)
    change ((moduleEvaluation A PUnit.{1} PUnit.unit).map
      (strictBarNormalizedGradedMap A J (η ≫ θ))).f q =
        ((moduleEvaluation A PUnit.{1} PUnit.unit).map
          (strictBarNormalizedGradedMap A J η ≫ strictBarNormalizedGradedMap A J θ)).f q at h
    simpa only [CategoryTheory.Functor.map_comp, HomologicalComplex.comp_f] using! h

/-- 元の正規化射影は、元のstrict自然変換に自然な同じ閉零射の族。 -/
def strictBarNormalizationNatTrans : strictBarUnnormalizedFunctor A J ⟶ strictBarNormalizedFunctor A J where
  app F := dgCoherentBarNormalizedModuleProjectionUnconditional A PUnit.{1} (smallStrictBarDiagram A F)
  naturality {F G} η := by
    apply (moduleEvaluation A PUnit.{1} PUnit.unit).map_injective
    apply HomologicalComplex.Hom.ext
    funext q
    simp only [CategoryTheory.Functor.map_comp, HomologicalComplex.comp_f]
    change ((moduleEvaluation A PUnit.{1} PUnit.unit).map (strictBarUnnormalizedMap A J η)).f q ≫
      ((moduleEvaluation A PUnit.{1} PUnit.unit).map
        (dgCoherentBarNormalizedModuleProjectionUnconditional A PUnit.{1} (smallStrictBarDiagram A G))).f q =
        ((moduleEvaluation A PUnit.{1} PUnit.unit).map
          (dgCoherentBarNormalizedModuleProjectionUnconditional A PUnit.{1} (smallStrictBarDiagram A F))).f q ≫
          ((moduleEvaluation A PUnit.{1} PUnit.unit).map (strictBarNormalizedMap A J η)).f q
    rw [strictBarUnnormalizedMap_component, strictBarNormalizedMap_component,
      dgCoherentBarNormalizedModuleProjection_evaluation_f,
      dgCoherentBarNormalizedModuleProjection_evaluation_f]
    have h := congrArg (fun f => ((moduleEvaluation A PUnit.{1} PUnit.unit).map f).f q)
      (strictBarGradedMap_projection A J η)
    simpa only [CategoryTheory.Functor.map_comp, HomologicalComplex.comp_f] using! h

/-- 同じ正規化射影の一点評価は、既存の指定鎖ホモトピー同値の逆向きの射。 -/
instance strictBarNormalizationNatTrans_quasiIso (F : J ⥤ ModuleCategory A PUnit.{1}) :
    QuasiIso ((moduleEvaluation A PUnit.{1} PUnit.unit).map
      ((strictBarNormalizationNatTrans A J).app F)) :=
  inferInstanceAs (QuasiIso ((smallStrictBarNormalizedInclusionPointHomotopyEquiv A F).symm.hom))

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
