module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.ConeTransformationMap
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.FatConeTransformationIso

/-!
概要：native な固定頂点の錐から定値始域の変換への同じ標準比較が同値であることを示す。
方針：両端固定の fat join 比較を経由する厳密な因子分解と、円柱の厳密な同型を使う。
規約：任意の形状と全追加パラメータを保持し、元の比較写像を変更しない。
使われ方：一般 coherent 小極限の全 Hom による普遍性の検証。

対応節は Kerodon 4.3（Tag 015M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions


/-- 同じ native な錐を fat 錐へ移した評価は、元の全評価の比較による前合成。 -/
lemma fixedApexFatConeComparison_evaluation {K X : SSet.{u}} (f : K ⟶ X) (z : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedApexFatConeComparison f z ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.fixedFatConeFamilyEvaluation f z =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedApexConeFamilyEvaluation f z ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinComparison Δ[0] K)).app X := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedApexFatConeComparison, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.fixedFatConeFamilyEvaluation, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedEndpointConeFatComparison, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_ι, ← Category.assoc]
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedApexEndpointConeSpaceIso]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedApexToEndpointConeSpace, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι]

/-- 元の標準比較は、同じ両端固定の fat 錐への比較と厳密な指数則の合成そのもの。 -/
lemma coneTransformationMap_factor {K X : SSet.{u}} (f : K ⟶ X) (z : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.coneTransformationMap f z = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedApexFatConeComparison f z ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.fatConeTransformationMap f z := by
  apply _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.sourceConstantTransformationPrism_injective
  have h : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.sourceConstantTransformationPrism (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.coneTransformationMap f z) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.coneParameterPrism (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedApexConeFamily f z)) := by
    simpa only [Category.id_comp] using _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.coneTransformationMap_prism (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedApexConeFamily f z))
  rw [h, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.fatConeTransformationMap_prism,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.coneParameterPrism, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.fatConeParameterPrism,
    fixedApexFatConeComparison_evaluation, uncurry_pre_app]
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.coneCylinderMap, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.fatConeCylinderMap, comp_whiskerRight, Category.assoc, Category.id_comp]

/-- 任意の形状の元の native な錐と、同じ定値始域の変換の標準比較は同値。 -/
lemma coneTransformationMap_isQCatEquivalence {K X : SSet.{u}} [Quasicategory X]
    (f : K ⟶ X) (z : X _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.coneTransformationMap f z) := by
  rw [coneTransformationMap_factor]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedApexFatConeComparison_isQCatEquivalence f z).comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.fatConeTransformationIso f z)).isQCatEquivalence

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
