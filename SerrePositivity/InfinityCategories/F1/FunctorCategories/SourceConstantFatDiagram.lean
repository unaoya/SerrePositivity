module

public import SerrePositivity.InfinityCategories.F1.Joins.FatConeParameterPrism
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.SourceConstantTransformationNaturality
public import SerrePositivity.InfinityCategories.Core.FatJoinTensorDesc

/-!
概要：定値始域の変換の全族を、頂点・図式を保つ fat join の錐の全族へ戻す。
方針：元の全円柱を左の一点付き円柱へ移し、右パラメータを保って貼り合わせる。
規約：頂点だけでなく全円柱と元の図式を厳密に保持する。
使われ方：錐と変換の標準比較の逆写像。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
variable {K X T : SSet.{u}} {f : K ⟶ X} {z : X _⦋0⦌}

/-- 元の変換全族から、同じ両端を持つ fat join 上の全図式を構成する。 -/
def sourceConstantFatDiagram
    (a : T ⟶ intervalMappingSpace (functorVertex (SSet.const z)) (functorVertex f)) :
    fatJoin Δ[0] K ⊗ T ⟶ X :=
  fatJoinDescTensorRight (SSet.const z : (Δ[0] : SSet.{u}) ⊗ T ⟶ X) (fst K T ≫ f)
    ((fatConeCylinderProjection K ▷ T) ≫ sourceConstantTransformationPrism a) (by
      rw [← Category.assoc, ← comp_whiskerRight, fatConeCylinderProjection_zero,
        comp_whiskerRight, Category.assoc, sourceConstantTransformationPrism_zero,
        SSet.comp_const, SSet.comp_const]) (by
      rw [← Category.assoc, ← comp_whiskerRight, fatConeCylinderProjection_one,
        comp_whiskerRight, Category.assoc, sourceConstantTransformationPrism_one])

/-- 戻した全図式の左端は同じ指定頂点。 -/
lemma sourceConstantFatDiagram_inl
    (a : T ⟶ intervalMappingSpace (functorVertex (SSet.const z)) (functorVertex f)) :
    (fatJoinInl Δ[0] K ▷ T) ≫ sourceConstantFatDiagram a = SSet.const z :=
  fatJoinInl_descTensorRight _ _ _ _ _

/-- 戻した全図式の右端は同じ元の図式。 -/
lemma sourceConstantFatDiagram_inr
    (a : T ⟶ intervalMappingSpace (functorVertex (SSet.const z)) (functorVertex f)) :
    (fatJoinInr Δ[0] K ▷ T) ≫ sourceConstantFatDiagram a = fst K T ≫ f :=
  fatJoinInr_descTensorRight _ _ _ _ _

/-- 戻した全図式の円柱は元の全変換の円柱そのもの。 -/
lemma sourceConstantFatDiagram_cylinder
    (a : T ⟶ intervalMappingSpace (functorVertex (SSet.const z)) (functorVertex f)) :
    (fatJoinCylinder Δ[0] K ▷ T) ≫ sourceConstantFatDiagram a =
      (fatConeCylinderProjection K ▷ T) ≫ sourceConstantTransformationPrism a :=
  fatJoinCylinder_descTensorRight _ _ _ _ _

/-- 元の円柱へ戻すと、指定された全変換の同じ円柱を厳密に回収する。 -/
lemma sourceConstantFatDiagram_prism
    (a : T ⟶ intervalMappingSpace (functorVertex (SSet.const z)) (functorVertex f)) :
    (fatConeCylinderMap K ▷ T) ≫ sourceConstantFatDiagram a =
      sourceConstantTransformationPrism a := by
  rw [fatConeCylinderMap, comp_whiskerRight, Category.assoc,
    sourceConstantFatDiagram_cylinder, ← Category.assoc, ← comp_whiskerRight]
  change (((fatConeCylinderIso K).inv ≫ (fatConeCylinderIso K).hom) ▷ T) ≫ _ = _
  rw [Iso.inv_hom_id, id_whiskerRight, Category.id_comp]

end SerrePositivity.InfinityCategories
