module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Sheaves.DiscreteElementsComparisonSpecifiedHom
public import SerrePositivity.InfinityCategories.Sheaves.SectionsOf
public import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.SetWeightSectionsEdgeNaturality
public import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.SetWeightMappedSectionsEdge
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.HomFiberInvertibility
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.LocalObjects
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.Reflection

/-!
概要：空間係数の局所 Hom 条件を離散重みの指定切断制限で判定する。
方針：全切断への G8 の比較を要素圏の制限と指定極限の比較に合成する。
  文献対応：HTT 5.5.4.20、6.2.2.6。
使われ方：無限圏の局所同値の検出。
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Project.FilteredExchange
open SerrePositivity.InfinityCategories.Project.SetWeightedTensors

namespace SerrePositivity.InfinityCategories.Sheaves

/-- 離散重みの指定射に対する局所 Hom 条件は、同じ指定切断制限の可逆性で判定される。 -/
@[cite HTT "5.5.4.20" (partial := special) "小さい通常の圏上の空間値前層と離散重み。"]
lemma discreteHom_precomposition_sections_detects_locality :
    ∀ {C : Type u} [SmallCategory C] {P Q : Cᵒᵖ ⥤ Type u}
      (φ : P ⟶ Q) (O : Presheaf C SpaceInfinity.{u})
      (hP : HasLimit (sectionsOfDiagram P O)) (hQ : HasLimit (sectionsOfDiagram Q O)),
      IsLocalForHom (discretePresheafHom φ) (functorVertex O) ↔
        IsInvertibleEdge (sectionsOf_map φ O hP hQ).toTruncated := by
  intro C hC P Q φ O hP hQ
  let U := SSet.uliftFunctor.{u + 1, u}
  let ρ := U.map (setWeightActualSectionsRestriction φ O)
  have h₀ : IsLocalForHom (discretePresheafHom φ) (functorVertex O) ↔
      IsQCatEquivalence ρ := by
    have he : Truncated.HomotopyCategory.homMk (SetWeight.spaceDiagramEdge φ).toTruncated =
        discretePresheafHom φ := by
      apply congrArg Truncated.HomotopyCategory.homMk
      apply Truncated.Edge.ext
      change (SetWeight.spaceDiagramEdge φ).edge =
        ((nerve.edgeMk φ).map (kanDiscretePresheafMap C)).edge
      exact (kanDiscretePresheafMap_edge φ).symm
    have hi := setWeightSectionsEquivalenceNatural_shapeIso φ O
    rw [he] at hi
    have hp := (SetWeight.sectionsEquivalenceNatural P O).isQCatEquivalence
    have hq := (SetWeight.sectionsEquivalenceNatural Q O).isQCatEquivalence
    constructor
    · intro h
      exact hq.cancel_left ((h.comp hp).ofFunctorIso hi)
    · intro h
      exact hp.cancel_right ((hq.comp h).ofFunctorIso hi.symm)
  let cP := sectionsOfCone P O hP
  let cQ := sectionsOfCone Q O hQ
  let hcP := sectionsOfCone_isLimit P O hP
  let hcQ := sectionsOfCone_isLimit Q O hQ
  let d := SetWeight.restrictSectionsCone φ O cQ
  let hv := SetWeight.restrictSectionsCone_vertex φ O cQ
  let e := SetWeight.sectionsConeMap φ O cP hcP cQ
  let δ := sectionsOf_map φ O hP hQ
  have he : coneApexEdgeAt e cQ.vertex hv = δ := by
    apply SSet.Edge.ext
    change (Eq.mp (congrArg (fun z ↦ SSet.Edge z cP.vertex) hv)
      (e.map (sliceOverProjection (SetWeight.diagram P O)))).edge = _
    rw [edge_source_transport_simplex hv]
    exact (setWeightSectionsMap_simplex φ O cP hcP cQ hcQ).symm
  have hi := sectionsLimitValue_normalizedShapeIso (SetWeight.diagram Q O)
    (SetWeight.diagram P O) (nerveMap φ.mapElements) (SetWeight.elementsMap_diagram φ O)
    cQ hcQ cP hcP d rfl hv e
  rw [he] at hi
  let f := spaceInfinityEdgeValue δ
  have hp := (sectionsLimitValueEquivalence (SetWeight.diagram P O) cP hcP).isQCatEquivalence.ulift
  have hq := (sectionsLimitValueEquivalence (SetWeight.diagram Q O) cQ hcQ).isQCatEquivalence.ulift
  have h₁ : IsQCatEquivalence ρ ↔ IsQCatEquivalence (U.map f) := by
    constructor
    · intro h
      exact hq.cancel_left ((h.comp hp).ofFunctorIso hi)
    · intro h
      exact hp.cancel_right ((hq.comp h).ofFunctorIso hi.symm)
  exact h₀.trans (h₁.trans ((isQCatEquivalence_ulift_iff_of_kan f).trans
    ((isInvertibleEdge_congr (spaceInfinityEdgeValue_edge δ)).symm.trans
      (coherentKanEdge_invertible_iff f)).symm))

end SerrePositivity.InfinityCategories.Sheaves
