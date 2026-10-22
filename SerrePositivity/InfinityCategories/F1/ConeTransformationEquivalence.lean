module

public import SerrePositivity.InfinityCategories.F1.ConeTransformationMap
public import SerrePositivity.InfinityCategories.F1.FatConeTransformationIso

/-!
概要：native な固定頂点の錐から定値始域の変換への同じ標準比較が同値であることを示す。
方針：両端固定の fat join 比較を経由する厳密な因子分解と、円柱の厳密な同型を使う。
規約：任意の形状と全追加パラメータを保持し、元の比較写像を変更しない。
使われ方：一般 coherent 小極限の全 Hom による普遍性の検証。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
open HomotopyLimits

/-- 同じ native な錐を fat 錐へ移した評価は、元の全評価の比較による前合成。 -/
lemma fixedApexFatConeComparison_evaluation {K X : SSet.{u}} (f : K ⟶ X) (z : X _⦋0⦌) :
    fixedApexFatConeComparison f z ≫ fixedFatConeFamilyEvaluation f z =
      fixedApexConeFamilyEvaluation f z ≫ (pre (fatJoinComparison Δ[0] K)).app X := by
  rw [fixedApexFatConeComparison, fixedFatConeFamilyEvaluation, Category.assoc,
    fixedEndpointConeFatComparison, vertexFiberMap_ι, ← Category.assoc]
  dsimp only [fixedApexEndpointConeSpaceIso]
  rw [fixedApexToEndpointConeSpace, vertexFiberLift_ι]

/-- 元の標準比較は、同じ両端固定の fat 錐への比較と厳密な指数則の合成そのもの。 -/
lemma coneTransformationMap_factor {K X : SSet.{u}} (f : K ⟶ X) (z : X _⦋0⦌) :
    coneTransformationMap f z = fixedApexFatConeComparison f z ≫ fatConeTransformationMap f z := by
  apply sourceConstantTransformationPrism_injective
  have h : sourceConstantTransformationPrism (coneTransformationMap f z) =
      coneParameterPrism (𝟙 (fixedApexConeFamily f z)) := by
    simpa only [Category.id_comp] using coneTransformationMap_prism (𝟙 (fixedApexConeFamily f z))
  rw [h, fatConeTransformationMap_prism,
    coneParameterPrism, fatConeParameterPrism,
    fixedApexFatConeComparison_evaluation, uncurry_pre_app]
  simp only [coneCylinderMap, fatConeCylinderMap, comp_whiskerRight, Category.assoc, Category.id_comp]

/-- 任意の形状の元の native な錐と、同じ定値始域の変換の標準比較は同値。 -/
lemma coneTransformationMap_isQCatEquivalence {K X : SSet.{u}} [Quasicategory X]
    (f : K ⟶ X) (z : X _⦋0⦌) : IsQCatEquivalence (coneTransformationMap f z) := by
  rw [coneTransformationMap_factor]
  exact (fixedApexFatConeComparison_isQCatEquivalence f z).comp
    (qCatEquivalenceOfIso (fatConeTransformationIso f z)).isQCatEquivalence

end SerrePositivity.InfinityCategories
