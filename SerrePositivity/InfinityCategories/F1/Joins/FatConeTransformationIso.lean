module

public import SerrePositivity.InfinityCategories.F1.Joins.FatConeFamilyCurry
public import SerrePositivity.InfinityCategories.F1.Joins.FatConePrismInjective
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.SourceConstantFatDiagram

/-!
概要：固定頂点の fat 錐と、定値始域から元の図式への変換の空間を厳密に同定する。
方針：同じ全円柱で両写像を定義し、円柱表示の一意性で両逆則を示す。
規約：任意の形状・追加パラメータで成立し、充填性を仮定しない。
使われ方：native な錐と定値始域の変換の標準比較の同値性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
open HomotopyLimits

/-- 元の fat 錐の全族を同じ定値始域の変換へ送る標準写像。 -/
def fatConeTransformationMap {K X : SSet.{u}} (f : K ⟶ X) (z : X _⦋0⦌) :
    fixedEndpointFatConeSpace f z ⟶
      intervalMappingSpace (functorVertex (SSet.const z)) (functorVertex f) :=
  sourceConstantTransformationCurry (fatConeParameterPrism (𝟙 (fixedEndpointFatConeSpace f z)))
    (fatConeParameterPrism_zero _) (fatConeParameterPrism_one _)

/-- 標準写像の全円柱は、元の fat 錐の円柱そのもの。 -/
lemma fatConeTransformationMap_prism {K X T : SSet.{u}} {f : K ⟶ X} {z : X _⦋0⦌}
    (a : T ⟶ fixedEndpointFatConeSpace f z) :
    sourceConstantTransformationPrism (a ≫ fatConeTransformationMap f z) =
      fatConeParameterPrism a := by
  rw [sourceConstantTransformationPrism_precomp, fatConeTransformationMap,
    sourceConstantTransformationPrism_curry, ← fatConeParameterPrism_precomp, Category.comp_id]

/-- 元の全変換を同じ fat 錐の全族へ戻す。 -/
def fatConeTransformationInverse {K X : SSet.{u}} (f : K ⟶ X) (z : X _⦋0⦌) :
    intervalMappingSpace (functorVertex (SSet.const z)) (functorVertex f) ⟶
      fixedEndpointFatConeSpace f z :=
  fixedFatConeFamilyCurry (sourceConstantFatDiagram (𝟙 _))
    (sourceConstantFatDiagram_inl _) (sourceConstantFatDiagram_inr _)

/-- 逆写像の円柱は元の全変換の同じ円柱。 -/
lemma fatConeTransformationInverse_prism {K X : SSet.{u}} (f : K ⟶ X) (z : X _⦋0⦌) :
    fatConeParameterPrism (fatConeTransformationInverse f z) =
      sourceConstantTransformationPrism (𝟙 (intervalMappingSpace
        (functorVertex (SSet.const z)) (functorVertex f))) := by
  rw [fatConeTransformationInverse, fixedFatConeFamilyCurry_prism, sourceConstantFatDiagram_prism]

/-- 頂点固定の fat 錐と同じ定値始域の変換の全空間は厳密に同型。 -/
def fatConeTransformationIso {K X : SSet.{u}} (f : K ⟶ X) (z : X _⦋0⦌) :
    fixedEndpointFatConeSpace f z ≅
      intervalMappingSpace (functorVertex (SSet.const z)) (functorVertex f) where
  hom := fatConeTransformationMap f z
  inv := fatConeTransformationInverse f z
  hom_inv_id := by
    apply fatConeParameterPrism_injective
    rw [fatConeParameterPrism_precomp, fatConeTransformationInverse_prism,
      ← sourceConstantTransformationPrism_precomp, Category.comp_id]
    simpa only [Category.id_comp] using
      fatConeTransformationMap_prism (𝟙 (fixedEndpointFatConeSpace f z))
  inv_hom_id := by
    apply sourceConstantTransformationPrism_injective
    rw [fatConeTransformationMap_prism, fatConeTransformationInverse_prism]

end SerrePositivity.InfinityCategories
