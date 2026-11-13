module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictSimplicialDerivedCocone
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.KanDiagramColimitTransport
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.FunctorComparisons.ClosedNerveFunctorNaturality
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.InvertibleEdgeIntervalExtension

/-!
# strict半自由図式への同じ実現余錐の公開

## 概要
半自由模型の元のstrict図式に、実現を頂点とするD(A)の指定余錐を返す。
## 方針
既存の半自由・射影的模型の同値の単位を使い、同じ頂点で余錐を輸送する。
## 規約
一点半自由加群と既存半自由複体の比較を使う。図式ごとの版。
## 使われ方
HA 1.2.4、HTT 4.2.4.1。IS-W2停止点1の入口。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet SerrePositivity.DifferentialGraded
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
variable (A : Type u) [CommRing A]
  (F : SimplicialObject (ClosedCategory A (SemifreeDGModules A PUnit.{1})))

/-- 元の同じstrict図式の台の一点加群図式。 -/
def pointSemifreeUnderlyingDiagram :=
  F ⋙ (dgFullSubcategoryInclusion A (RightModule A PUnit.{1})
    (dgModuleSemifreeProperty A PUnit.{1})).onClosed

/-- 同じ台の各加群は、既存の半自由性から射影的。 -/
theorem pointSemifreeUnderlyingDiagram_projective (j : SimplexCategoryᵒᵖ) :
    moduleHomotopicallyProjective A PUnit.{1} ((pointSemifreeUnderlyingDiagram A F).obj j) :=
  dgSemifreeModule_isProjective A PUnit.{1} (ForgetEnrichment.to (Complex A) (F.obj j))

/-- 元の半自由図式を、同じ小さい添字のnerveから読む。 -/
def pointSemifreeStrictDiagram :=
  (smallDiagramShapeIso.{u} (nerve SimplexCategoryᵒᵖ)).hom ≫
    strictDiagramNerve SimplexCategoryᵒᵖ _ F ≫
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveInclusion A (SemifreeDGModules A PUnit.{1})

/-- 射影的模型を経由した図式と、元の同じ半自由図式との既存単位による同型。 -/
def pointSemifreeRealizationDiagramIso :
    FunctorIso (strictSimplicialDerivedDiagram A (pointSemifreeUnderlyingDiagram A F)
      (pointSemifreeUnderlyingDiagram_projective A F))
      (pointSemifreeStrictDiagram A F ≫ (semifreePointEquivalence A).hom) := by
  let e := (dgSemifreeToProjectiveNerve_isQCatEquivalence A PUnit.{1}).choose
  have h := (e.homInvIso.precomp (pointSemifreeStrictDiagram A F)).postcomp
    (semifreePointEquivalence A).hom
  have hd : specifiedProjectiveDiagram A PUnit.{1}
      (F := smallStrictBarDiagram A (pointSemifreeUnderlyingDiagram A F))
      (fun t => pointSemifreeUnderlyingDiagram_projective A F (t.down.down.obj 0)) =
        pointSemifreeStrictDiagram A F ≫ e.hom := by
    let i := dgFullSubcategoryInclusion A (RightModule A PUnit.{1}) (dgModuleProjectiveProperty A PUnit.{1})
    apply (cancel_mono (SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map i)).1
    rw [specifiedProjectiveDiagram, fullInclusionLift_comp]
    change _ = (smallDiagramShapeIso.{u} _).hom ≫ strictDiagramNerve SimplexCategoryᵒᵖ _ F ≫
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveInclusion A (SemifreeDGModules A PUnit.{1}) ≫
        SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
          (dgFullSubcategoryInclusion A (RightModule A PUnit.{1}) (dgModuleSemifreeProperty A PUnit.{1})))
    rw [closedNerveInclusion_dgFunctor]
    rfl
  change FunctorIso (specifiedProjectiveDiagram A PUnit.{1} _ ≫
    ((e.inv ≫ (semifreePointEquivalence A).hom))) _
  rw [hd, ← Category.assoc]
  simpa only [Category.assoc, Category.comp_id] using h

/-- 指定単位の同じ代表辺を、そのまま可逆区間へ延長する。 -/
def pointSemifreeRealizationIntervalExtension :=
  exists_kanEquivalenceInterval_extension_of_invertibleEdge
    ((SSet.yonedaEquiv (X := (ihom ((SSet.uliftFunctor.{u + 1, u}).obj
      ((SSet.uliftFunctor.{u, 0}).obj (nerve SimplexCategoryᵒᵖ)))).obj (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A))).symm
      (pointSemifreeRealizationDiagramIso A F).edge.edge) (by
      apply (isInvertibleEdge_congr (f := (pointSemifreeRealizationDiagramIso A F).edge)
        (by
          change SSet.yonedaEquiv _ = _
          exact Equiv.apply_symm_apply _ _)).mpr
      exact (pointSemifreeRealizationDiagramIso A F).edge_isInvertible)

/-- 同じ図式の単位の代表辺を保持する可逆円柱。 -/
def pointSemifreeRealizationCylinder := uncurry (pointSemifreeRealizationIntervalExtension A F).choose

/-- 可逆円柱は、単位の同じ辺を厳密に保持する。辺の類は既存edge_homMkで元の単位。 -/
theorem pointSemifreeRealizationCylinder_unit :
    equivalenceIntervalEdge ≫ (pointSemifreeRealizationIntervalExtension A F).choose =
      (SSet.yonedaEquiv (X := (ihom ((SSet.uliftFunctor.{u + 1, u}).obj
      ((SSet.uliftFunctor.{u, 0}).obj (nerve SimplexCategoryᵒᵖ)))).obj (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A))).symm
      (pointSemifreeRealizationDiagramIso A F).edge.edge :=
  (pointSemifreeRealizationIntervalExtension A F).choose_spec

/-- 可逆円柱の両端は、指定した同じ二つの図式である。 -/
theorem pointSemifreeRealizationCylinder_endpoints :
    equivalenceCylinderEndpoint _ false ≫ pointSemifreeRealizationCylinder A F =
      strictSimplicialDerivedDiagram A (pointSemifreeUnderlyingDiagram A F)
        (pointSemifreeUnderlyingDiagram_projective A F) ∧
    equivalenceCylinderEndpoint _ true ≫ pointSemifreeRealizationCylinder A F =
      pointSemifreeStrictDiagram A F ≫ (semifreePointEquivalence A).hom := by
  constructor
  · apply functorVertex_injective
    rw [pointSemifreeRealizationCylinder, functorVertex_equivalenceCylinderEndpoint_uncurry]
    have h := congrArg (fun z => stdSimplex.δ (1 : Fin 2) ≫ z)
      (pointSemifreeRealizationCylinder_unit A F)
    rw [← Category.assoc, equivalenceIntervalEdge_zero] at h
    have hv := congrArg SSet.yonedaEquiv h
    rw [stdSimplex.yonedaEquiv_δ_comp] at hv
    erw [Equiv.apply_symm_apply] at hv
    exact hv.trans (pointSemifreeRealizationDiagramIso A F).edge.src_eq
  · apply functorVertex_injective
    rw [pointSemifreeRealizationCylinder, functorVertex_equivalenceCylinderEndpoint_uncurry]
    have h := congrArg (fun z => stdSimplex.δ (0 : Fin 2) ≫ z)
      (pointSemifreeRealizationCylinder_unit A F)
    rw [← Category.assoc, equivalenceIntervalEdge_one] at h
    have hv := congrArg SSet.yonedaEquiv h
    rw [stdSimplex.yonedaEquiv_δ_comp] at hv
    erw [Equiv.apply_symm_apply] at hv
    exact hv.trans (pointSemifreeRealizationDiagramIso A F).edge.tgt_eq

/-- 元の全余錐を左端に厳密に保持する、円柱全体の余極限余錐の延長。 -/
def pointSemifreeRealizationExtension :=
  exists_colimitCocone_extension_of_precompositionEquivalence (pointSemifreeRealizationCylinder A F)
    (equivalenceCylinderEndpoint _ false) (isPrecompositionEquivalence_equivalenceCylinderEndpoint _ false)
    (coherentCoconeOfDiagramEq (pointSemifreeRealizationCylinder_endpoints A F).1.symm
      (strictSimplicialDerivedCocone A (pointSemifreeUnderlyingDiagram A F)
        (pointSemifreeUnderlyingDiagram_projective A F)))
    ((coherentCoconeOfDiagramEq_isColimit_iff _ _).mp
      (strictSimplicialDerivedCocone_isColimit A (pointSemifreeUnderlyingDiagram A F)
        (pointSemifreeUnderlyingDiagram_projective A F)))

/-- 元のstrict図式上の実際の余錐。右端への制限なので同じ円柱の全成分を持つ。 -/
def strictSemifreeRealizationCocone :=
  coherentCoconeOfDiagramEq (pointSemifreeRealizationCylinder_endpoints A F).2
    ((pointSemifreeRealizationExtension A F).choose.restrict (equivalenceCylinderEndpoint _ true))

/-- 左端の脚・高次成分は、計算済みの同じ余錐に厳密に一致する。 -/
theorem pointSemifreeRealizationExtension_source :
    ((pointSemifreeRealizationExtension A F).choose.restrict
      (equivalenceCylinderEndpoint _ false)).val =
      (strictSimplicialDerivedCocone A (pointSemifreeUnderlyingDiagram A F)
        (pointSemifreeUnderlyingDiagram_projective A F)).val := by
  rw [(pointSemifreeRealizationExtension A F).choose_spec.2.1,
    coherentCoconeOfDiagramEq_val]

/-- 同じ円柱の右端の指定余錐はD(A)で余極限となる。 -/
theorem strictSemifreeRealizationCocone_isColimit :
    IsColimitCone (strictSemifreeRealizationCocone A F) := by
  apply (coherentCoconeOfDiagramEq_isColimit_iff _ _).mp
  have := sliceUnderRestrict_trivialKanFibration_of_precompositionEquivalence
    (pointSemifreeRealizationCylinder A F) (equivalenceCylinderEndpoint _ true)
    (isPrecompositionEquivalence_equivalenceCylinderEndpoint _ true)
  exact ((qCatEquivalenceOfTrivialKanFibration (sliceUnderRestrict
    (pointSemifreeRealizationCylinder A F) (equivalenceCylinderEndpoint _ true))).isInitialVertex_iff
      (pointSemifreeRealizationExtension A F).choose).mp
        (pointSemifreeRealizationExtension A F).choose_spec.1

/-- 図式の単位による輸送でも、元の実現を表す同じ頂点を保持する。 -/
theorem strictSemifreeRealizationCocone_vertex :
    (strictSemifreeRealizationCocone A F).vertex =
      (strictSimplicialDerivedCocone A (pointSemifreeUnderlyingDiagram A F)
        (pointSemifreeUnderlyingDiagram_projective A F)).vertex := by
  rw [strictSemifreeRealizationCocone, coherentCoconeOfDiagramEq_vertex, JoinCocone.vertex_restrict,
    (pointSemifreeRealizationExtension A F).choose_spec.2.2, coherentCoconeOfDiagramEq_vertex]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
