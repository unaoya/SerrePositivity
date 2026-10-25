module

public import SerrePositivity.InfinityCategories.F1.Diagrams.CocartesianKanWeightedUnitData
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorDescentOver

/-!
概要：元の cocartesian 全空間から、同じ Kan 値 weighted nerve への全族単位を降下する。
方針：元の universal scaffold の前合成同値で、指定 scaffold 単位を相対降下する。
規約：底を厳密に保ち、元の scaffold 単位への回収を相対関手空間内で返す。
使われ方：Ind-S (5) の全族単位を fiber ごとに元の Kan 単位へ照合する。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 元の全空間から Kan 値 weighted nerve への実単位と、指定 scaffold 単位の相対回収。 -/
lemma exists_cocartesianKanWeightedUnit {I : Type u} [Category.{u} I]
    {E : SSet.{u}} (p : E ⟶ nerve I) [CocartesianFibration p]
    (R : SSet.{u} ⥤ KanObject.{u}) (η : 𝟭 SSet.{u} ⟶ R ⋙ kanObjectForget) :
    ∃ f : E ⟶ weightedNerve
        ((cocartesianStrictTransportDiagram p ⋙ R) ⋙ kanObjectForget),
      ∃ hf : f ≫ weightedNerveProjection
        ((cocartesianStrictTransportDiagram p ⋙ R) ⋙ kanObjectForget) = p,
      Nonempty (VertexIso
        (relativeFunctorVertex _ (simplicialReplacementProjection
          (cocartesianStrictTransportDiagram p)) (cocartesianUniversalScaffold p ≫ f)
          (by rw [Category.assoc, hf, cocartesianUniversalScaffold_projection]))
        (relativeFunctorVertex _ _ (cocartesianKanWeightedScaffoldUnit p R η)
          (cocartesianKanWeightedScaffoldUnit_projection p R η))) := by
  have : ∀ c, KanComplex
      (((cocartesianStrictTransportDiagram p ⋙ R) ⋙ kanObjectForget).obj c) :=
    fun c => (R.obj ((cocartesianStrictTransportDiagram p).obj c)).isKanComplex
  exact exists_relativeFunctorExtension_over_of_precompositionEquivalence
    (weightedNerveProjection ((cocartesianStrictTransportDiagram p ⋙ R) ⋙ kanObjectForget)) p
    (simplicialReplacementProjection (cocartesianStrictTransportDiagram p))
    (cocartesianUniversalScaffold p) (cocartesianUniversalScaffold_projection p)
    (cocartesianUniversalScaffold_isPrecompositionEquivalence p)
    (cocartesianKanWeightedScaffoldUnit p R η) (cocartesianKanWeightedScaffoldUnit_projection p R η)

end SerrePositivity.InfinityCategories
