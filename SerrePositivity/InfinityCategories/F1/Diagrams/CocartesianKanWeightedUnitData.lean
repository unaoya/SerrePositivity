module

public import SerrePositivity.InfinityCategories.F1.Weighted.NerveMapComparison
public import SerrePositivity.InfinityCategories.F1B.CocartesianScaffold.Comparison
public import SerrePositivity.InfinityCategories.F1B.CocartesianScaffold.UniversalScaffoldFiber
public import SerrePositivity.InfinityCategories.F1.KanModels.KanPointHomNaturality

/-!
概要：元の cocartesian strict transport の Kan 置換単位を scaffold 全体へ写す。
方針：同じ自然変換を係数 weighted nerve へ写し、元の taut scaffold と合成する。
規約：元の図式・単位・底への射影を全て固定する。
使われ方：Ind-S (5) の元の全族から空間値の復元への単位の構成。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 元の strict transport の全係数に、同じ Kan 置換単位を適用する。 -/
def cocartesianKanWeightedUnitTransformation {I : Type u} [Category.{u} I]
    {E : SSet.{u}} (p : E ⟶ nerve I) (R : SSet.{u} ⥤ KanObject.{u})
    (η : 𝟭 SSet.{u} ⟶ R ⋙ kanObjectForget) :
    cocartesianStrictTransportDiagram p ⟶
      (cocartesianStrictTransportDiagram p ⋙ R) ⋙ kanObjectForget :=
  Functor.whiskerLeft (cocartesianStrictTransportDiagram p) η

/-- 元の scaffold 全体から、同じ Kan 値 weighted nerve への指定単位写像。 -/
def cocartesianKanWeightedScaffoldUnit {I : Type u} [Category.{u} I]
    {E : SSet.{u}} (p : E ⟶ nerve I) (R : SSet.{u} ⥤ KanObject.{u})
    (η : 𝟭 SSet.{u} ⟶ R ⋙ kanObjectForget) :
    simplicialReplacement (cocartesianStrictTransportDiagram p) ⟶
      weightedNerve ((cocartesianStrictTransportDiagram p ⋙ R) ⋙ kanObjectForget) :=
  tautScaffold (cocartesianStrictTransportDiagram p) ≫
    weightedNerveMap (cocartesianKanWeightedUnitTransformation p R η)

/-- 元の scaffold の単位写像は底の射影を厳密に保持する。 -/
lemma cocartesianKanWeightedScaffoldUnit_projection {I : Type u} [Category.{u} I]
    {E : SSet.{u}} (p : E ⟶ nerve I) (R : SSet.{u} ⥤ KanObject.{u})
    (η : 𝟭 SSet.{u} ⟶ R ⋙ kanObjectForget) :
    cocartesianKanWeightedScaffoldUnit p R η ≫
      weightedNerveProjection ((cocartesianStrictTransportDiagram p ⋙ R) ⋙ kanObjectForget) =
    simplicialReplacementProjection (cocartesianStrictTransportDiagram p) := by
  rw [cocartesianKanWeightedScaffoldUnit, Category.assoc, weightedNerveMap_projection,
    tautScaffold_projection]

end SerrePositivity.InfinityCategories
