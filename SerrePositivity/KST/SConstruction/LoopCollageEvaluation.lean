module
public import SerrePositivity.KST.SConstruction.EnrichedFunctorCollageNerve
public import SerrePositivity.KST.SConstruction.SuspensionLoopEnrichedPostcomposition

/-! # Loop の有向 collage から suspension 側への評価
概要：下段は suspension、上段は元の対象、交差写像は元の逆随伴で評価する。
方針：上下段の豊穣関手性と随伴の両変数の豊穣自然性で合成を照合する。
規約：標的は全点つき単体集合の coherent nerve。標的全体の Kan 性は主張しない。
使われ方：局所 Kan な collage 内で合成した全入力円柱を、元の suspension 構造射へ運ぶ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open Spectra
open SerrePositivity.InfinityCategories
open scoped Simplicial

local instance loopCollageEvaluation_pointed_simplicialCategory :
    SimplicialCategory PointedSimplicialSet.{u} := PointedEnrichment.simplicialCategory

/-- 元の Kan 対象と元の写像空間を保持する全部分圏の豊穣包含。 -/
def pointedKanInclusionEnriched :
    EnrichedFunctor SSet.{u} PointedKanObject.{u} PointedSimplicialSet.{u} where
  obj X := X.obj
  map X Y := 𝟙 (SimplicialCategory.sHom X Y)
  map_id X := Category.comp_id _
  map_comp X Y Z := by
    change eComp SSet X.obj Y.obj Z.obj ≫ 𝟙 _ =
      (𝟙 (SimplicialCategory.sHom X Y) ⊗ₘ 𝟙 (SimplicialCategory.sHom Y Z)) ≫
        eComp SSet X.obj Y.obj Z.obj
    simp only [Category.comp_id, tensorHom_id, id_whiskerRight, Category.id_comp]

/-- Loop collage の下段は suspension、上段は元の対象として評価する。 -/
def loopCollageEvaluationObj
    (X : EnrichedFunctorCollageCategory pointedKanLoopEnrichedFunctor.{u}) :
    PointedSimplicialSet.{u} :=
  match X with
  | .inl X => _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension X.obj
  | .inr Y => Y.obj

/-- 交差写像空間には元の suspension–loop 随伴の逆を適用する。 -/
def loopCollageEvaluationMap
    (X Y : EnrichedFunctorCollageCategory pointedKanLoopEnrichedFunctor.{u}) :
    SimplicialCategory.sHom X Y ⟶
      (PointedObject.basedHom (loopCollageEvaluationObj X) (loopCollageEvaluationObj Y)).right :=
  match X, Y with
  | .inl X, .inl Y => (suspensionHom X.obj Y.obj).right
  | .inl X, .inr Y => (suspensionLoopMappingIso X.obj Y.obj).inv
  | .inr X, .inl Y =>
      enrichedCollageEmptyMap (PointedObject.basedHom X.obj (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension Y.obj)).right
  | .inr X, .inr Y => 𝟙 (SimplicialCategory.sHom X Y)

/-- 全写像パラメータの合成を保つ、loop collage から元の点つき模型への豊穣評価。 -/
def loopCollageEvaluation :
    EnrichedFunctor SSet.{u}
      (EnrichedFunctorCollageCategory pointedKanLoopEnrichedFunctor.{u})
      PointedSimplicialSet.{u} where
  obj := loopCollageEvaluationObj
  map := loopCollageEvaluationMap
  map_id X := by
    rcases X with X | X
    · exact suspensionHom_simplicial_id X.obj
    · exact Category.comp_id _
  map_comp X Y Z := by
    change enrichedFunctorCollageComp pointedKanLoopEnrichedFunctor X Y Z ≫
        loopCollageEvaluationMap X Z =
      (loopCollageEvaluationMap X Y ⊗ₘ loopCollageEvaluationMap Y Z) ≫
        eComp SSet (loopCollageEvaluationObj X) (loopCollageEvaluationObj Y)
          (loopCollageEvaluationObj Z)
    rcases X with X | X <;> rcases Y with Y | Y <;> rcases Z with Z | Z
    · exact suspensionHom_simplicial_comp X.obj Y.obj Z.obj
    · exact suspensionLoopMappingIso_inv_enriched_pre X.obj Y.obj Z.obj
    · apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro x
      exact PEmpty.elim x.2
    · exact suspensionLoopMappingIso_inv_enriched_post X.obj Y.obj Z.obj
    · apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro x
      exact PEmpty.elim x.1
    · apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro x
      exact PEmpty.elim x.1
    · apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro x
      exact PEmpty.elim x.2
    · change eComp SSet X.obj Y.obj Z.obj ≫ 𝟙 _ =
        (𝟙 (SimplicialCategory.sHom X Y) ⊗ₘ 𝟙 (SimplicialCategory.sHom Y Z)) ≫
          eComp SSet X.obj Y.obj Z.obj
      simp only [Category.comp_id, tensorHom_id, id_whiskerRight, Category.id_comp]

/-- 下段の評価は、元の包含の後の元の suspension 豊穣関手。 -/
lemma loopCollageEvaluation_bottom :
    (enrichedFunctorCollageBottom pointedKanLoopEnrichedFunctor.{u}).comp SSet
        loopCollageEvaluation =
      pointedKanInclusionEnriched.comp SSet suspensionEnrichedFunctor := by
  refine EnrichedFunctor.ext SSet (fun _ => ?_) ?_
  · rfl
  · intro X Y
    change (𝟙 (SimplicialCategory.sHom X Y) ≫ (suspensionHom X.obj Y.obj).right) ≫ 𝟙 _ =
      𝟙 (SimplicialCategory.sHom X Y) ≫ (suspensionHom X.obj Y.obj).right
    exact Category.comp_id _

/-- 上段の評価は、元の対象・射を持つ全部分圏の豊穣包含。 -/
lemma loopCollageEvaluation_top :
    (enrichedFunctorCollageTop pointedKanLoopEnrichedFunctor.{u}).comp SSet
        loopCollageEvaluation = pointedKanInclusionEnriched := by
  refine EnrichedFunctor.ext SSet (fun _ => ?_) ?_
  · rfl
  · intro X Y
    change (𝟙 (SimplicialCategory.sHom X Y) ≫ 𝟙 _) ≫ 𝟙 _ = 𝟙 _
    simp only [Category.comp_id]

/-- Collage 内の全入力単体を、元の suspension と標的の coherent nerve へ写す射。 -/
def loopCollageEvaluationNerve :
    EnrichedFunctorCollageInfinity pointedKanLoopEnrichedFunctor.{u} ⟶
      SimplicialNerve PointedSimplicialSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap loopCollageEvaluation

/-- 下段の coherent nerve の評価は全単体で suspension の像。 -/
lemma loopCollageEvaluationNerve_bottom :
    enrichedFunctorCollageBottomInfinity pointedKanLoopEnrichedFunctor.{u} ≫
        loopCollageEvaluationNerve =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap pointedKanInclusionEnriched ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap suspensionEnrichedFunctor := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (enrichedFunctorCollageBottom pointedKanLoopEnrichedFunctor.{u}) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap loopCollageEvaluation = _
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_comp, loopCollageEvaluation_bottom, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_comp]

/-- 上段の coherent nerve の評価は全単体で元の対象・射の包含。 -/
lemma loopCollageEvaluationNerve_top :
    enrichedFunctorCollageTopInfinity pointedKanLoopEnrichedFunctor.{u} ≫
        loopCollageEvaluationNerve = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap pointedKanInclusionEnriched := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (enrichedFunctorCollageTop pointedKanLoopEnrichedFunctor.{u}) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap loopCollageEvaluation = _
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_comp, loopCollageEvaluation_top]

/-- 元の loop 値の点つき射を、collage の実際の下段から上段への射として表す。 -/
def loopCollageCrossMap (X Y : PointedKanObject.{u}) (f : X.obj ⟶ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y.obj) :
    (enrichedFunctorCollageBottom pointedKanLoopEnrichedFunctor).obj X ⟶
      (enrichedFunctorCollageTop pointedKanLoopEnrichedFunctor).obj Y :=
  ForgetEnrichment.homOf SSet
    (C := EnrichedFunctorCollage pointedKanLoopEnrichedFunctor)
    (X := (Sum.inl X : EnrichedFunctorCollage pointedKanLoopEnrichedFunctor))
    (Y := Sum.inr Y)
    ((SSet.unitHomEquiv _).symm (pointedHomVertexEquiv X.obj (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y.obj) f))

/-- Collage の交差射は元の点つき射の写像空間の頂点を厳密に回収する。 -/
lemma loopCollageCrossMap_vertex (X Y : PointedKanObject.{u})
    (f : X.obj ⟶ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y.obj) :
    SimplicialCategory.homEquiv' _ _ (loopCollageCrossMap X Y f) =
      pointedHomVertexEquiv X.obj (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y.obj) f := by
  change (SSet.unitHomEquiv _)
      ((SSet.unitHomEquiv _).symm (pointedHomVertexEquiv X.obj (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y.obj) f)) = _
  exact Equiv.apply_symm_apply _ _

/-- 元の値域への射影は、交差射から元の loop 値の点つき射そのものを回収する。 -/
lemma loopCollageCrossMap_projection (X Y : PointedKanObject.{u})
    (f : X.obj ⟶ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y.obj) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor
      (enrichedFunctorCollageProjection pointedKanLoopEnrichedFunctor)).map
        (loopCollageCrossMap X Y f)).hom = f := by
  apply (pointedHomVertexEquiv X.obj (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y.obj)).injective
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor_vertex
    (enrichedFunctorCollageProjection pointedKanLoopEnrichedFunctor) (loopCollageCrossMap X Y f)
  change pointedHomVertexEquiv X.obj (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y.obj)
      (((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor
        (enrichedFunctorCollageProjection pointedKanLoopEnrichedFunctor)).map
          (loopCollageCrossMap X Y f)).hom) =
    SimplicialCategory.homEquiv' _ _ (loopCollageCrossMap X Y f) at h
  exact h.trans (loopCollageCrossMap_vertex X Y f)

/-- Suspension 側の評価は、元の射の元の逆随伴そのものを厳密に回収する。 -/
lemma loopCollageCrossMap_evaluation (X Y : PointedKanObject.{u})
    (f : X.obj ⟶ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y.obj) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor loopCollageEvaluation).map (loopCollageCrossMap X Y f) =
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv X.obj Y.obj).symm f := by
  apply (pointedHomVertexEquiv (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension X.obj) Y.obj).injective
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor_vertex loopCollageEvaluation
    (loopCollageCrossMap X Y f)
  change pointedHomVertexEquiv (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension X.obj) Y.obj
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor loopCollageEvaluation).map
        (loopCollageCrossMap X Y f)) =
    (suspensionLoopMappingIso X.obj Y.obj).inv.app (Opposite.op ⦋0⦌)
      (SimplicialCategory.homEquiv' _ _ (loopCollageCrossMap X Y f)) at h
  rw [loopCollageCrossMap_vertex] at h
  exact h.trans (suspensionLoopMappingIso_inv_vertex f)

end SerrePositivity.KST.SConstruction
