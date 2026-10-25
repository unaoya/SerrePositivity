module

public import SerrePositivity.InfinityCategories.F1.Diagrams.CocartesianKanWeightedUnit
public import SerrePositivity.InfinityCategories.F1.Weighted.KanEdgewiseComparison
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.DirectKanCoefficients
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.SmallLeftUnstraighteningLift

/-!
概要：直値 Kan 図式の weighted nerve から、その小さい unstraightening へ実射を供給する。
方針：edgewise 共通解像の左比較を既存の実比較へ送り、右比較で底を固定して降下する。
規約：係数の反転を底の反転と混同せず、元の coherent 図式を厳密に使う。
使われ方：Ind-S (5) の元の全族単位の標的を指定 unstraightening へ接続する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 反転した係数から、直値図式の同じ小さい復元への実射。 -/
def smallReversedWeightedKanUnstraighteningComparison
    {I : Type u} [Category.{u} I] (F : I ⥤ KanObject.{u}) :
    weightedNerve (F ⋙ kanObjectOpFunctor ⋙ kanObjectForget) ⟶
      smallLeftUnstraightening (kanDiagramCoherentNerve F) :=
  smallLeftUnstraighteningLift _ (reversedWeightedKanUnstraighteningComparison F)

/-- 同じ実比較は元の底を厳密に保つ。 -/
lemma smallReversedWeightedKanUnstraighteningComparison_projection
    {I : Type u} [Category.{u} I] (F : I ⥤ KanObject.{u}) :
    smallReversedWeightedKanUnstraighteningComparison F ≫
      smallLeftUnstraighteningProjection (kanDiagramCoherentNerve F) =
      weightedNerveProjection (F ⋙ kanObjectOpFunctor ⋙ kanObjectForget) :=
  smallLeftUnstraighteningLift_projection _ _ _
    (reversedWeightedKanUnstraighteningComparison_projection F)

/-- 共通解像上の同じ比較を相対的に回収する、直値 weighted nerve からの実射。 -/
lemma exists_kanWeightedUnstraighteningUnit
    {I : Type u} [Category.{u} I] (F : I ⥤ KanObject.{u}) :
    ∃ (f : weightedNerve (F ⋙ kanObjectForget) ⟶
      smallLeftUnstraightening (kanDiagramCoherentNerve F))
      (hf : f ≫ smallLeftUnstraighteningProjection (kanDiagramCoherentNerve F) =
        weightedNerveProjection (F ⋙ kanObjectForget)),
      Nonempty (VertexIso
        (relativeFunctorVertex (smallLeftUnstraighteningProjection (kanDiagramCoherentNerve F))
          (weightedNerveProjection (F ⋙ kanEdgewiseFunctor ⋙ kanObjectForget))
          (weightedKanEdgewiseRight F ≫ f)
          (by rw [Category.assoc, hf, weightedKanEdgewiseRight_projection]))
        (relativeFunctorVertex (smallLeftUnstraighteningProjection (kanDiagramCoherentNerve F))
          (weightedNerveProjection (F ⋙ kanEdgewiseFunctor ⋙ kanObjectForget))
          (weightedKanEdgewiseLeft F ≫ smallReversedWeightedKanUnstraighteningComparison F)
          (by rw [Category.assoc, smallReversedWeightedKanUnstraighteningComparison_projection,
            weightedKanEdgewiseLeft_projection]))) := by
  exact exists_relativeFunctorExtension_over_of_precompositionEquivalence
    (smallLeftUnstraighteningProjection (kanDiagramCoherentNerve F))
    (weightedNerveProjection (F ⋙ kanObjectForget))
    (weightedNerveProjection (F ⋙ kanEdgewiseFunctor ⋙ kanObjectForget))
    (weightedKanEdgewiseRight F) (weightedKanEdgewiseRight_projection F)
    (weightedKanEdgewiseRight_isPrecompositionEquivalence F)
    (weightedKanEdgewiseLeft F ≫ smallReversedWeightedKanUnstraighteningComparison F)
    (by rw [Category.assoc, smallReversedWeightedKanUnstraighteningComparison_projection,
      weightedKanEdgewiseLeft_projection])

/-- 元の cocartesian 全族から指定した直値 Kan 図式の小さい復元への実射と厳密な底。 -/
lemma exists_cocartesianKanUnstraighteningUnit_over
    {I : Type u} [Category.{u} I] {E : SSet.{u}}
    (p : E ⟶ nerve I) [CocartesianFibration p]
    (R : SSet.{u} ⥤ KanObject.{u}) (η : 𝟭 SSet.{u} ⟶ R ⋙ kanObjectForget) :
    ∃ f : E ⟶ smallLeftUnstraightening
      (kanDiagramCoherentNerve (cocartesianStrictTransportDiagram p ⋙ R)),
      f ≫ smallLeftUnstraighteningProjection
        (kanDiagramCoherentNerve (cocartesianStrictTransportDiagram p ⋙ R)) = p := by
  obtain ⟨a, ha, _⟩ := exists_cocartesianKanWeightedUnit p R η
  obtain ⟨b, hb, _⟩ := exists_kanWeightedUnstraighteningUnit
    (cocartesianStrictTransportDiagram p ⋙ R)
  exact ⟨a ≫ b, by rw [Category.assoc, hb, ha]⟩

end SerrePositivity.InfinityCategories
