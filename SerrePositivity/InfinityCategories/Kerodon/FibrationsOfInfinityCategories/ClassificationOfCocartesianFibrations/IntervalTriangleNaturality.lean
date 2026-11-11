module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.IntervalCompositionTriangle

/-!
概要：元の固定成分 Hom の正方形・三角形への制限は、全パラメーターの前合成と可換。
方針：元の prism の評価とテンソルの交換則で計算する。
規約：同じ第一三角形への写像の普遍族を保持する。
使われ方：第二三角形の外ホーン制限を同じ合成三角形写像と結ぶ。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 元の関手圏 Hom の prism は、追加パラメーターの前合成と厳密に可換。 -/
lemma intervalFunctorHomPrism_precomp {A T B X : SSet.{u}} {F G : B ⟶ X}
    (i : A ⟶ T) (f : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G)) :
    ((Δ[1] ⊗ B) ◁ i) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalFunctorHomPrism f = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalFunctorHomPrism (i ≫ f) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨⟨t, b⟩, a⟩
  rfl

variable (F G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianTransportDiagramCategory (ULift.{u} (Fin 2)))
local notation "c" => (ULift.up (1 : Fin 2))
variable (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramValue F c))
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramValue G c))) _⦋0⦌)
local notation "E" => (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianHomIntervalEvaluation F G c) v)

/-- 同じ固定成分 fiber の標準正方形は、全パラメーターの前合成と可換。 -/
lemma cocartesianIntervalHomSquare_precomp {A T : SSet.{u + 1}} (i : A ⟶ T) (f : T ⟶ E) :
    ((Δ[1] ⊗ Δ[1]) ◁ i) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianIntervalHomSquare F G v f =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianIntervalHomSquare F G v (i ≫ f) := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianIntervalHomSquare _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianHomFixedComponentPrism
  rw [← Category.assoc, whisker_exchange, Category.assoc, intervalFunctorHomPrism_precomp,
    Category.assoc]

/-- 同じ二つの実際の三角形への制限は、全パラメーターの前合成と可換。 -/
lemma cocartesianIntervalHomTriangle_precomp {A T : SSet.{u + 1}}
    (j : Fin 2) (i : A ⟶ T) (f : T ⟶ E) :
    (Δ[2] ◁ i) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianIntervalHomTriangle F G v j f =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianIntervalHomTriangle F G v j (i ≫ f) := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianIntervalHomTriangle
  rw [← Category.assoc, whisker_exchange, Category.assoc, cocartesianIntervalHomSquare_precomp]

/-- 同じ第一三角形の普遍制限写像は、任意の族でも元の第一三角形を展開で回収する。 -/
lemma cocartesianIntervalCompositionTriangleMap_uncurry {T : SSet.{u + 1}} (f : T ⟶ E) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.innerTriangleExtensionUncurry (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianIntervalCompositionTriangleMap F G v) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianIntervalHomTriangle F G v 0 f := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.innerTriangleExtensionUncurry
  rw [Category.assoc, uncurry_natural_left]
  change (Δ[2] ◁ f) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.innerTriangleExtensionUncurry
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianIntervalCompositionTriangleFamily F G v (𝟙 E)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianIntervalCompositionTriangleFamily_uncurry,
    cocartesianIntervalHomTriangle_precomp, Category.comp_id]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
