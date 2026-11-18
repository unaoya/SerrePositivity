module

public import SerrePositivity.InfinityCategories.Sheaves.MovingIndexPointClass
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.FaithfulNerveReadout
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.PointCoslicePostIso
public import SerrePositivity.InfinityCategories.Sheaves.NativeRightKanDensityComposition
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.RelativeFunctorPostEquivalence
public import SerrePositivity.InfinityCategories.Sheaves.WeightedSectionsNativeLimitGlobalComparison
public import SerrePositivity.InfinityCategories.Sheaves.NativeLeftSectionsTransportCone
public import SerrePositivity.InfinityCategories.Sheaves.WeightedSectionsOriginalLeftLimit
public import SerrePositivity.InfinityCategories.Sheaves.DiscretePresheafHom
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.RelativeFunctorIsPullbackIso
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.ExtOne
public import SerrePositivity.InfinityCategories.Sheaves.DiscreteRightKanNerveReadout
public import SerrePositivity.InfinityCategories.Sheaves.DiscreteRightKanVertexClasses
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.CosliceHomotopy

/-!
概要：元の離散前層の変換に対して、指定した右 Kan の添字の両端を同じ係数図式の上で照合する。
方針：指定した辺と添字の座標に既存の評価則を適用する。
使われ方：離散前層の重み付き切断の自然性。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories
set_option autoImplicit false
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
open SerrePositivity.InfinityCategories.Sheaves
open SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

namespace SerrePositivity.InfinityCategories.Sheaves

def discreteWeightedSectionsMovingIndexCondition
    {C : Type u} [SmallCategory C] {P Q : Cᵒᵖ ⥤ Type u} (φ : P ⟶ Q) : Prop :=
  let U := SSet.uliftFunctor.{u + 1, u}
  let b := nerveOppositeIso (C := C)
  let F := U.map b.hom ≫ discretePresheaf P
  let G := U.map b.hom ≫ discretePresheaf Q
  let a := U.map ((smallLeftUnstraighteningBaseIso b (discretePresheaf P)).hom ≫
    smallUnstraighteningFunctorHom (discretePresheafHom φ) ≫
    (smallLeftUnstraighteningBaseIso b (discretePresheaf Q)).inv)
  let δ := SSet.opFunctor.map (yonedaInfinityMap (nerve C))
  let e' := edgeOp (nativeDiscreteEdge φ).toTruncated
  let η : (Δ[1] : SSet.{u + 1}) ⟶ (PresheafInfinity (nerve C)).op :=
    SSet.yonedaEquiv.symm e'.edge
  ∀ (he₀ : stdSimplex.δ (1 : Fin 2) ≫ η =
        SSet.yonedaEquiv.symm (SSet.opObjEquiv.symm (functorVertex G)))
    (he₁ : stdSimplex.δ (0 : Fin 2) ≫ η =
        SSet.yonedaEquiv.symm (SSet.opObjEquiv.symm (functorVertex F))),
    rightKanMovingIndexFace δ η he₀ he₁
      (a ≫ leftElementsRightKanComparison G) (leftElementsRightKanComparison F)

private theorem discreteWeightedSectionsMovingIndex_projections
    {C : Type u} [SmallCategory C] {P Q : Cᵒᵖ ⥤ Type u} (φ : P ⟶ Q) :
    let U := SSet.uliftFunctor.{u + 1, u}
    let b := nerveOppositeIso (C := C)
    let F := U.map b.hom ≫ discretePresheaf P
    let G := U.map b.hom ≫ discretePresheaf Q
    let a := U.map ((smallLeftUnstraighteningBaseIso b (discretePresheaf P)).hom ≫
      smallUnstraighteningFunctorHom (discretePresheafHom φ) ≫
      (smallLeftUnstraighteningBaseIso b (discretePresheaf Q)).inv)
    let δ := SSet.opFunctor.map (yonedaInfinityMap (nerve C))
    (a ≫ leftElementsRightKanComparison G) ≫
        rightKanProjection δ (SSet.opObjEquiv.symm (functorVertex G)) =
      leftElementsRightKanComparison F ≫
        rightKanProjection δ (SSet.opObjEquiv.symm (functorVertex F)) := by
  intro U b F G a δ
  change (a ≫ leftElementsRightKanComparison G) ≫ rightKanProjection _ _ =
    leftElementsRightKanComparison F ≫ rightKanProjection _ _
  rw [Category.assoc, leftElementsRightKanComparison_projection,
    leftElementsRightKanComparison_projection]
  rw [← Category.assoc]
  apply congrArg (fun k => k ≫ (uliftOppositeIso (nerve C)).hom)
  let α := discretePresheafHom φ
  let i := smallLeftUnstraighteningBaseIso b (discretePresheaf P)
  let j := smallLeftUnstraighteningBaseIso b (discretePresheaf Q)
  have hJ : j.inv ≫ smallLeftUnstraighteningProjection G =
      smallLeftUnstraighteningProjection (discretePresheaf Q) ≫ b.inv := by
    apply (cancel_epi j.hom).mp
    rw [Iso.hom_inv_id_assoc, ← Category.assoc, smallLeftUnstraighteningBaseIso_projection,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have he : (i.hom ≫ smallUnstraighteningFunctorHom α ≫ j.inv) ≫
      smallLeftUnstraighteningProjection G = smallLeftUnstraighteningProjection F := by
    simp only [Category.assoc]
    rw [hJ, ← Category.assoc (smallUnstraighteningFunctorHom α),
      smallUnstraighteningFunctorHom_projection, ← Category.assoc i.hom,
      smallLeftUnstraighteningBaseIso_projection, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  change U.map (i.hom ≫ smallUnstraighteningFunctorHom α ≫ j.inv) ≫
    U.map (smallLeftUnstraighteningProjection G) = _
  simp only [← CategoryTheory.Functor.map_comp]
  exact congrArg U.map he

private theorem discreteWeightedSectionsMovingIndex_of_localLabels
    {C : Type u} [SmallCategory C] {P Q : Cᵒᵖ ⥤ Type u} (φ : P ⟶ Q) :
    let U := SSet.uliftFunctor.{u + 1, u}
    let b := nerveOppositeIso (C := C)
    let t := U.mapIso b.symm ≪≫ uliftOppositeIso (nerve C)
    let s := t.symm ≪≫ nerveAsSmallIso.{u, u + 1} Cᵒᵖ
    let p : AsSmall.{u + 1} Q.Elements ⥤ AsSmall.{u + 1} Cᵒᵖ :=
      AsSmall.down ⋙ Functor.Elements.π Q ⋙ AsSmall.up
    let r := nerveMap p ≫ s.inv
    let F := U.map b.hom ≫ discretePresheaf P
    let G := U.map b.hom ≫ discretePresheaf Q
    let a := U.map ((smallLeftUnstraighteningBaseIso b (discretePresheaf P)).hom ≫
      smallUnstraighteningFunctorHom (discretePresheafHom φ) ≫
      (smallLeftUnstraighteningBaseIso b (discretePresheaf Q)).inv)
    let δ := SSet.opFunctor.map (yonedaInfinityMap (nerve C))
    let e' := edgeOp (nativeDiscreteEdge φ).toTruncated
    let η : (Δ[1] : SSet.{u + 1}) ⟶ (PresheafInfinity (nerve C)).op :=
      SSet.yonedaEquiv.symm e'.edge
    let v₀ := SSet.opObjEquiv.symm (functorVertex G)
    let v₁ := SSet.opObjEquiv.symm (functorVertex F)
    let j₀ := a ≫ leftElementsRightKanComparison G
    let j₁ := leftElementsRightKanComparison F
    let hj := discreteWeightedSectionsMovingIndex_projections φ
    (∀ (he₀ : stdSimplex.δ (1 : Fin 2) ≫ η = SSet.yonedaEquiv.symm v₀)
       (he₁ : stdSimplex.δ (0 : Fin 2) ≫ η = SSet.yonedaEquiv.symm v₁)
       (i : rightKanShape δ v₀ ⟶ nerve (AsSmall.{u + 1} Q.Elements)),
       i ≫ r = rightKanProjection δ v₀ → IsPrecompositionEquivalence i →
       let q₀ := sliceUnderProjection (SSet.yonedaEquiv.symm v₀)
       let k := j₀ ≫ rightKanProjection δ v₀
       let r₀ := sliceUnderRestrict η (stdSimplex.δ (1 : Fin 2)) ≫
         eqToHom (congrArg sliceUnder he₀)
       let hw := rightKanMovingIndex_target_section δ η he₀ he₁ j₀ j₁ hj
       let w := (j₁ ≫ pullback.fst (sliceUnderProjection (SSet.yonedaEquiv.symm v₁)) δ) ≫
         (eqToHom (congrArg sliceUnder he₁.symm) ≫ cosliceEdgeSection η)
       ∀ x : (U.obj (smallLeftUnstraightening F)) _⦋0⦌,
         (pullback.lift (w ≫ r₀) k hw.2.1 ≫ i).app _ x = (j₀ ≫ i).app _ x) →
    discreteWeightedSectionsMovingIndexCondition φ := by
  intro U b t s p r F G a δ e' η v₀ v₁ j₀ j₁ hj hl
  intro he₀ he₁
  obtain ⟨i, hi, ei, hrf⟩ := exists_discreteRightKan_nerve_readout Q
  letI : LeftFibration r := hrf
  letI : (AsSmall.down : AsSmall.{u + 1} Q.Elements ⥤ Q.Elements).IsEquivalence :=
    (AsSmall.equiv (C := Q.Elements)).isEquivalence_inverse
  letI : (AsSmall.up : Cᵒᵖ ⥤ AsSmall.{u + 1} Cᵒᵖ).IsEquivalence :=
    (AsSmall.equiv (C := Cᵒᵖ)).isEquivalence_functor
  letI : p.Faithful := by dsimp [p]; infer_instance
  have hs : r ≫ s.hom = nerveMap p := by
    dsimp only [r]
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply rightKanMovingIndexFace_of_selectedSource δ η he₀ he₁ j₀ j₁ hj
  exact rightKanMovingIndex_selectedSource_of_nerve_readout p r s.hom hs δ η he₀ he₁
    j₀ j₁ hj i hi ei (hl he₀ he₁ i hi ei)

private theorem discreteWeightedSectionsMovingIndex_of_pointHomMk
    {C : Type u} [SmallCategory C] {P Q : Cᵒᵖ ⥤ Type u} (φ : P ⟶ Q) :
    let U := SSet.uliftFunctor.{u + 1, u}
    let b := nerveOppositeIso (C := C)
    let t := U.mapIso b.symm ≪≫ uliftOppositeIso (nerve C)
    let s := t.symm ≪≫ nerveAsSmallIso.{u, u + 1} Cᵒᵖ
    let p : AsSmall.{u + 1} Q.Elements ⥤ AsSmall.{u + 1} Cᵒᵖ :=
      AsSmall.down ⋙ Functor.Elements.π Q ⋙ AsSmall.up
    let r := nerveMap p ≫ s.inv
    let F := U.map b.hom ≫ discretePresheaf P
    let G := U.map b.hom ≫ discretePresheaf Q
    let a := U.map ((smallLeftUnstraighteningBaseIso b (discretePresheaf P)).hom ≫
      smallUnstraighteningFunctorHom (discretePresheafHom φ) ≫
      (smallLeftUnstraighteningBaseIso b (discretePresheaf Q)).inv)
    let δ := SSet.opFunctor.map (yonedaInfinityMap (nerve C))
    let e' := edgeOp (nativeDiscreteEdge φ).toTruncated
    let η : (Δ[1] : SSet.{u + 1}) ⟶ (PresheafInfinity (nerve C)).op :=
      SSet.yonedaEquiv.symm e'.edge
    let v₀ := SSet.opObjEquiv.symm (functorVertex G)
    let v₁ := SSet.opObjEquiv.symm (functorVertex F)
    let j₀ := a ≫ leftElementsRightKanComparison G
    let j₁ := leftElementsRightKanComparison F
    let hj := discreteWeightedSectionsMovingIndex_projections φ
    (∀ (he₀ : stdSimplex.δ (1 : Fin 2) ≫ η = SSet.yonedaEquiv.symm v₀)
       (he₁ : stdSimplex.δ (0 : Fin 2) ≫ η = SSet.yonedaEquiv.symm v₁),
       let q₀ := sliceUnderProjection (SSet.yonedaEquiv.symm v₀)
       let k := j₀ ≫ rightKanProjection δ v₀
       let r₀ := sliceUnderRestrict η (stdSimplex.δ (1 : Fin 2)) ≫
         eqToHom (congrArg sliceUnder he₀)
       let hw := rightKanMovingIndex_target_section δ η he₀ he₁ j₀ j₁ hj
       let w := (j₁ ≫ pullback.fst (sliceUnderProjection (SSet.yonedaEquiv.symm v₁)) δ) ≫
         (eqToHom (congrArg sliceUnder he₁.symm) ≫ cosliceEdgeSection η)
       ∀ x : (U.obj (smallLeftUnstraightening F)) _⦋0⦌,
       let l := pullback.lift (w ≫ r₀) k hw.2.1
       let x₀ := l.app (Opposite.op ⦋0⦌) x
       let x₁ := j₀.app (Opposite.op ⦋0⦌) x
       let z := (rightKanProjection δ v₀).app (Opposite.op ⦋0⦌) x₀
       let f : (vertexFiber q₀ (δ.app _ z)) _⦋0⦌ :=
         ⟨(pullback.fst q₀ δ).app _ x₀, by
           rw [pinchedConstant_zero]
           have hc : pullback.fst q₀ δ ≫ q₀ = pullback.snd q₀ δ ≫ δ := pullback.condition
           exact ConcreteCategory.congr_hom (NatTrans.congr_app hc _) x₀⟩
       let g : (vertexFiber q₀ (δ.app _ z)) _⦋0⦌ :=
         ⟨(pullback.fst q₀ δ).app _ x₁, by
           rw [pinchedConstant_zero]
           have hp : l ≫ rightKanProjection δ v₀ = k := pullback.lift_snd _ _ _
           have hxy : (rightKanProjection δ v₀).app _ x₀ =
               (rightKanProjection δ v₀).app _ x₁ :=
             ConcreteCategory.congr_hom (NatTrans.congr_app hp _) x
           have hc : pullback.fst q₀ δ ≫ q₀ = pullback.snd q₀ δ ≫ δ := pullback.condition
           exact (ConcreteCategory.congr_hom (NatTrans.congr_app hc _) x₁).trans
             (congrArg (fun z' => δ.app (Opposite.op ⦋0⦌) z') hxy.symm)⟩
       Truncated.HomotopyCategory.homMk (cosliceFiberEdge _ _ f) =
         Truncated.HomotopyCategory.homMk (cosliceFiberEdge _ _ g)) →
    discreteWeightedSectionsMovingIndexCondition φ := by
  intro U b t s p r F G a δ e' η v₀ v₁ j₀ j₁ hj hpoint
  apply discreteWeightedSectionsMovingIndex_of_localLabels φ
  intro he₀ he₁ i hi ei q₀ k r₀ hw w x
  let l := pullback.lift (w ≫ r₀) k hw.2.1
  let x₀ := l.app (Opposite.op ⦋0⦌) x
  let x₁ := j₀.app (Opposite.op ⦋0⦌) x
  have hp : l ≫ rightKanProjection δ v₀ = k := pullback.lift_snd _ _ _
  have hxy : (rightKanProjection δ v₀).app _ x₀ =
      (rightKanProjection δ v₀).app _ x₁ :=
    ConcreteCategory.congr_hom (NatTrans.congr_app hp _) x
  have hr : i ≫ nerveMap p = rightKanProjection δ v₀ ≫ s.hom := by
    have hs : r ≫ s.hom = nerveMap p := by
      dsimp only [r]
      rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [← hs, ← Category.assoc, hi]
  change i.app _ x₀ = i.app _ x₁
  apply rightKanReadout_elements_vertices_eq_of_cosliceHomMk_eq Q δ v₀ i s.hom hr x₀ x₁ hxy
  exact hpoint he₀ he₁ x

/-- 元の離散前層の変換に対して、指定した右 Kan の添字の両端を同じ係数図式の上で照合する。
Kerodon §9.3（Tag 06FR）、§7.3（Tag 02Y9）。HTT 5.1.5.6 の指定離散重みの比較。 -/
lemma discreteWeightedSectionsMovingIndex_actual
    {C : Type u} [SmallCategory C] {P Q : Cᵒᵖ ⥤ Type u} (φ : P ⟶ Q) :
    discreteWeightedSectionsMovingIndexCondition φ := by
  apply discreteWeightedSectionsMovingIndex_of_pointHomMk φ
  intro he₀ he₁ q₀ k r₀ hw w d l x₀ x₁ z f g
  let U := SSet.uliftFunctor.{u+1,u}
  let i := nerveOppositeIso (C := C)
  let F := U.map i.hom ≫ discretePresheaf P
  let G := U.map i.hom ≫ discretePresheaf Q
  let a := U.map ((smallLeftUnstraighteningBaseIso i (discretePresheaf P)).hom ≫
    smallUnstraighteningFunctorHom (discretePresheafHom φ) ≫
    (smallLeftUnstraighteningBaseIso i (discretePresheaf Q)).inv)
  let j₀ := a ≫ leftElementsRightKanComparison G
  let j₁ := leftElementsRightKanComparison F
  let δ := SSet.opFunctor.map (yonedaInfinityMap (nerve C))
  let e := SSet.Edge.ofTruncated (X := (PresheafInfinity (nerve C)).op)
    (edgeOp (nativeDiscreteEdge φ).toTruncated)
  exact rightKanMovingIndex_pointComp_of_projectedLegs δ e j₀ j₁
    (discreteWeightedSectionsMovingIndex_projections φ)
    (discreteRightKan_projectedLegs_comp φ) he₀ he₁ d f g rfl rfl

end SerrePositivity.InfinityCategories.Sheaves
