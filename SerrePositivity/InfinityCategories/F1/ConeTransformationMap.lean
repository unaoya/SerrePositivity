module

public import SerrePositivity.InfinityCategories.F1.ConeParameterPrism
public import SerrePositivity.InfinityCategories.F1.SourceConstantTransformationNaturality

/-!
概要：頂点固定の native な錐の空間から、同じ定値始域の変換空間への標準比較を構成する。
方針：錐の恒等族の全円柱を二段階で curry する。
規約：元の図式・頂点・全追加パラメータを保持する。同値性は別工程。
使われ方：一般 coherent 小極限の native な全 Hom 判定。
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

/-- 元の全錐の族を、同じ定値始域から元の図式への変換にする。 -/
def coneTransformationMap {K X : SSet.{u}} (f : K ⟶ X) (z : X _⦋0⦌) :
    fixedApexConeFamily f z ⟶
      intervalMappingSpace (functorVertex (SSet.const z)) (functorVertex f) :=
  sourceConstantTransformationCurry (coneParameterPrism (𝟙 (fixedApexConeFamily f z)))
    (coneParameterPrism_zero _) (coneParameterPrism_one _)

/-- 同じ比較の任意の部分族の円柱は、元の全錐の族の円柱そのもの。 -/
lemma coneTransformationMap_prism {K X T : SSet.{u}} {f : K ⟶ X} {z : X _⦋0⦌}
    (a : T ⟶ fixedApexConeFamily f z) :
    sourceConstantTransformationPrism (a ≫ coneTransformationMap f z) = coneParameterPrism a := by
  rw [sourceConstantTransformationPrism_precomp, coneTransformationMap,
    sourceConstantTransformationPrism_curry, ← coneParameterPrism_precomp, Category.comp_id]

end SerrePositivity.InfinityCategories
