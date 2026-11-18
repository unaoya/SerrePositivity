module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SmallLeftUnstraighteningBaseIso
public import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.SetWeightRelativeUniverse
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.RelativeFunctorPostEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.RelativeFunctorVertexIsoProjection
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.GrothendieckConstruction.UniverseLeftFibration
public import SerrePositivity.InfinityCategories.Sheaves.DiscretePresheafHom
public import SerrePositivity.InfinityCategories.Sheaves.NativeWeightedSectionsLeftLimit
public import SerrePositivity.InfinityCategories.Sheaves.PresheafYonedaShapeIso
public import SerrePositivity.InfinityCategories.Project.SetWeightedTensors.DiscreteElementsNerveLeftFibration

/-!
概要：離散前層の右 Kan 添字から、同じ底上の通常の要素圏の nerve への比較を得る。
方針：既存の要素圏比較の合成を、左ファイブレーションの上で反転する。
使われ方：R06.2 の指定始点の比較。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
open SerrePositivity.InfinityCategories.Project.SetWeightedTensors
open SerrePositivity.InfinityCategories.Sheaves

namespace SerrePositivity.InfinityCategories.Sheaves

/-- 離散前層の右 Kan 添字から、同じ底上の通常の要素圏の nerve への比較を得る。
HTT 3.3.2、Kerodon Construction 5.3.4.11（Tag 0373）の集合値前層の場合。 -/
lemma exists_discreteRightKan_nerve_readout
    {C : Type u} [SmallCategory C] (P : Cᵒᵖ ⥤ Type u) :
    let U := SSet.uliftFunctor.{u + 1, u}
    let b := nerveOppositeIso (C := C)
    let t := U.mapIso b.symm ≪≫ uliftOppositeIso (nerve C)
    let s := t.symm ≪≫ nerveAsSmallIso.{u, u + 1} Cᵒᵖ
    let p : AsSmall.{u + 1} P.Elements ⥤ AsSmall.{u + 1} Cᵒᵖ :=
      AsSmall.down ⋙ Functor.Elements.π P ⋙ AsSmall.up
    let r := nerveMap p ≫ s.inv
    let F := U.map b.hom ≫ discretePresheaf P
    let δ := SSet.opFunctor.map (yonedaInfinityMap (nerve C))
    let v := SSet.opObjEquiv.symm (functorVertex F)
    ∃ i : rightKanShape δ v ⟶ nerve (AsSmall.{u + 1} P.Elements),
      i ≫ r = rightKanProjection δ v ∧
      IsPrecompositionEquivalence i ∧ LeftFibration r := by
  intro U b t s p r F δ v
  let ξ := nerveAsSmallIso.{u, u + 1} P.Elements
  let q := rightKanProjection δ v
  let c := smallLeftUnstraighteningBaseIso b (discretePresheaf P)
  have hr : r = ξ.inv ≫ U.map (nerveMap (Functor.Elements.π P)) ≫ t.hom := by
    change nerveMap p ≫ ((nerveAsSmallIso.{u, u + 1} Cᵒᵖ).inv ≫ t.hom) = _
    rw [← Category.assoc]
    rfl
  let π := nerveMap (Functor.Elements.π P)
  haveI : LeftFibration π := elements_projection_leftFibration P
  letI : LeftFibration (U.map π) := leftFibration_uliftFunctor_map π
  let e : Arrow.mk (U.map π) ≅ Arrow.mk r := Arrow.isoMk ξ t (by
    change ξ.hom ≫ r = U.map π ≫ t.hom
    rw [hr, Iso.hom_inv_id_assoc])
  haveI : LeftFibration r :=
    ⟨(leftFibrations.arrow_mk_iso_iff e).mp (LeftFibration.mem (p := U.map π))⟩
  haveI : LeftFibration q :=
    ⟨leftFibrations.pullback_snd _ _ (LeftFibration.mem (p := sliceUnderProjection _))⟩
  haveI : Quasicategory (rightKanShape δ v) := quasicategory_of_innerFibration q
  let j := ξ.inv ≫ U.map (SetWeight.elementsComparisonNatural P) ≫ U.map c.inv ≫
    leftElementsRightKanComparison F
  have hc : c.inv ≫ smallLeftUnstraighteningProjection F =
      smallLeftUnstraighteningProjection (discretePresheaf P) ≫ b.inv := by
    apply (cancel_epi c.hom).mp
    rw [Iso.hom_inv_id_assoc, ← Category.assoc, smallLeftUnstraighteningBaseIso_projection,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hj : j ≫ q = r := by
    change (ξ.inv ≫ U.map (SetWeight.elementsComparisonNatural P) ≫ U.map c.inv ≫
      leftElementsRightKanComparison F) ≫ rightKanProjection _ _ = _
    simp only [Category.assoc, leftElementsRightKanComparison_projection]
    have hElem : SetWeight.elementsComparisonNatural P ≫
        (smallLeftUnstraighteningProjection (discretePresheaf P) ≫ b.inv) =
          π ≫ b.inv := by
      rw [← Category.assoc]
      exact congrArg (fun a => a ≫ b.inv) (SetWeight.elementsComparisonNatural_projection P)
    rw [← Category.assoc (U.map c.inv), ← Functor.map_comp, hc]
    rw [← Category.assoc (U.map (SetWeight.elementsComparisonNatural P)), ← Functor.map_comp]
    rw [hElem, hr, Functor.map_comp]
    simp only [Category.assoc]
    rfl
  have ej : IsQCatEquivalence j :=
    (qCatEquivalenceOfIso ξ.symm).isQCatEquivalence.comp
      ((SetWeight.elementsComparisonNatural_isPrecompositionEquivalence P).isQCatEquivalence.ulift.comp
        ((qCatEquivalenceOfIso (U.mapIso c.symm)).isQCatEquivalence.comp
          (leftElementsRightKanComparison_isQCatEquivalence F)))
  obtain ⟨i, hi, ⟨hu⟩, _⟩ :=
    exists_relativeFunctorInverse_of_precompositionEquivalence
      r q j hj ej.isPrecompositionEquivalence
  have hf := relativeFunctorVertexIsoImage r r (j ≫ i) (𝟙 _)
    (by rw [Category.assoc, hi, hj]) (Category.id_comp r) hu
  have hId : IsQCatEquivalence (𝟙 (nerve (AsSmall.{u + 1} P.Elements))) :=
    (qCatEquivalenceOfIso (Iso.refl _)).isQCatEquivalence
  exact ⟨i, hi, (ej.cancel_left (hId.ofFunctorIso hf.symm)).isPrecompositionEquivalence, inferInstance⟩

end SerrePositivity.InfinityCategories.Sheaves
